local png = {}

local floor, ceil, abs = math.floor, math.ceil, math.abs

local function memo(f)
    local cache = setmetatable({}, {__mode = "kv"})
    return function(...)
        local key = table.concat({...}, "-")
        if not cache[key] then
            cache[key] = f(...)
        end
        return cache[key]
    end
end

local function int(bytes)
    local n = 0
    for i = 1, #bytes do
        n = 256 * n + bytes:sub(i, i):byte()
    end
    return n
end
int = memo(int)

local function bits(b, width)
    local s = ""
    if type(b) == "number" then
        for i = 1, width do
            s = (b % 2) .. s
            b = floor(b / 2)
        end
    else
        for i = 1, #b do
            s = s .. bits(b:sub(i, i):byte(), 8):reverse()
        end
    end
    return s
end
bits = memo(bits)

local function bint(str)
    return tonumber(str, 2) or 0
end
bint = memo(bint)

local function byte_stream(raw)
    local curr = 0
    return {
        read = function(_, n)
            local chunk = raw:sub(curr + 1, curr + n)
            curr = curr + n
            return chunk
        end,
        seek = function(_, n, whence)
            if whence == "beg" then
                curr = n
            elseif whence == "end" then
                curr = #raw
            else
                curr = curr + n
            end
        end,
        is_empty = function()
            return curr >= #raw
        end
    }
end

local function bit_stream(raw, offset)
    local curr = 0
    offset = offset or 0
    return {
        read = function(_, n, rev)
            local start = floor(curr / 8) + offset + 1
            local slice = raw:sub(start, start + ceil(n / 8))
            local b = bits(slice):sub(curr % 8 + 1, curr % 8 + n)
            curr = curr + n
            return rev and b or b:reverse()
        end,
        seek = function(_, n)
            if n == "beg" then
                curr = 0
            elseif n == "end" then
                curr = 8 * #raw
            else
                curr = curr + n
            end
        end,
        is_empty = function()
            return curr >= 8 * #raw
        end
    }
end

local function output_stream()
    local buf, pos = {}, 0
    local S = {}
    function S.write(_, bytes)
        for i = 1, #bytes do
            buf[#buf + 1] = bytes:sub(i, i)
        end
        pos = pos + #bytes
    end
    function S.back_copy(_, dist, length)
        local st = pos - dist + 1
        local cp = {}
        for i = st, st + length - 1 do
            cp[#cp + 1] = buf[i]
        end
        local s = table.concat(cp)
        local rep = math.ceil(length / #s)
        S.write(_, s:rep(rep):sub(1, length))
    end
    function S.raw()
        return table.concat(buf)
    end
    return S
end

local CHANNELS = {[0] = 1, [2] = 3, [3] = 1, [4] = 2, [6] = 4}
local PT_W = 8
local CL_ORDER = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15}

local function prefix_table(codes, alpha)
    local pt = {}
    local function handle_long(cds, alp)
        for i, code in ipairs(cds) do
            if #code > PT_W then
                local group = {}
                for j = i, #cds do
                    group[#group + 1] = {cds[j], alp[j]}
                end
                local done = 0
                while done < #group do
                    local pre = group[done + 1][1]:sub(1, PT_W)
                    local same = {}
                    for _, p in ipairs(group) do
                        if p[1]:sub(1, PT_W) == pre then
                            same[#same + 1] = p
                        end
                    end
                    local tail_c, tail_a = {}, {}
                    for _, p in ipairs(same) do
                        tail_c[#tail_c + 1], tail_a[#tail_a + 1] = p[1]:sub(PT_W + 1), p[2]
                    end
                    pt[pre] = {rest = prefix_table(tail_c, tail_a), unused = 0}
                    done = done + #same
                end
                break
            end
        end
    end
    handle_long(codes, alpha)
    for i, length in ipairs(codes) do
        local entry = {value = alpha[i], unused = PT_W - length}
        local bitstr = bits((i == 1 and 0 or (entry.value)), length)
        if entry.unused == 0 then
            pt[bitstr] = entry
        else
            for n = 0, 2 ^ entry.unused - 1 do
                pt[bitstr .. bits(n, entry.unused)] = entry
            end
        end
    end
    return pt
end

local function build_huffman(stream, lens, alpha)
    local tbl = prefix_table(lens, alpha)
    return function()
        local e, rest = tbl[stream:read(PT_W, true)], tbl
        rest = e.rest
        stream:seek(-e.unused)
        while rest do
            e = rest[stream:read(PT_W, true)]
            rest = e.rest
            stream:seek(-e.unused)
        end
        return e.value
    end
end

local function decode_lengths(stream, count, decoder)
    local out = {}
    while #out < count do
        local v = decoder(stream)
        if v < 16 then
            out[#out + 1] = v
        elseif v == 16 then
            local r = bint(stream:read(2)) + 3
            for _ = 1, r do
                out[#out + 1] = out[#out]
            end
        elseif v == 17 then
            local r = bint(stream:read(3)) + 3
            for _ = 1, r do
                out[#out + 1] = 0
            end
        else
            local r = bint(stream:read(7)) + 11
            for _ = 1, r do
                out[#out + 1] = 0
            end
        end
    end
    return out
end

local function inflate(stream)
    local out = output_stream()
    repeat
        local final = bint(stream:read(1))
        local btype = bint(stream:read(2))
        if btype ~= 2 then
            error("only dynamic Huffman")
        end

        local hlit = bint(stream:read(5)) + 257
        local hdist = bint(stream:read(5)) + 1
        local hclen = bint(stream:read(4)) + 4

        local cl_lens = {}
        for i = 1, hclen do
            cl_lens[#cl_lens + 1] = bint(stream:read(3))
        end
        local cl_dec = build_huffman(stream, cl_lens, CL_ORDER)

        local lit_lens = decode_lengths(stream, hlit, cl_dec)
        local dst_lens = decode_lengths(stream, hdist, cl_dec)

        local lit_dec = build_huffman(stream, lit_lens, {})
        local dst_dec = build_huffman(stream, dst_lens, {})

        while true do
            local sym = lit_dec(stream)
            if sym < 256 then
                out:write(string.char(sym))
            elseif sym == 256 then
                break
            else
                local length = (sym == 285 and 258) or (3 + sym - 257 + bint(stream:read(extra_bits(sym))))
                local dist = dst_dec(stream)
                local d = bint(stream:read(extra_bits(dist))) + 1
                out:back_copy(d, length)
            end
        end
    until final == 1
    return out:raw()
end

local function process_header(s, img)
    s:seek(8, "beg")
    img.width = int(s:read(4))
    img.height = int(s:read(4))
    img.bit_depth = int(s:read(1))
    img.color_type = int(s:read(1))
    img.channels = CHANNELS[img.color_type]
    s:seek(5, "cur")
end

local function process_palette(s, img)
    local len = int(s:read(4))
    s:seek(4, "cur")
    img.plte = {string.byte(s:read(len), 1, -1)}
    s:seek(4, "cur")
end

local function process_trns(s, img)
    local len = int(s:read(4))
    s:seek(4, "cur")
    img.trns = s:read(len)
    s:seek(4, "cur")
end

local function process_data(s, img)
    local len = int(s:read(4))
    s:seek(4, "cur")
    local zstream = output_stream()
    repeat
        zstream:write(s:read(len))
        s:seek(4, "cur")
        len = int(s:read(4))
    until s:read(4) ~= "IDAT"
    s:seek(-8, "cur")
    local raw = zstream:raw()
    local bstr = bit_stream(raw, 2)
    img.data = inflate(bstr)
end

local function process_chunk(s, img)
    local len = int(s:read(4))
    local typ = s:read(4)
    s:seek(-8, "cur")
    if typ == "IHDR" then
        process_header(s, img)
    elseif typ == "PLTE" then
        process_palette(s, img)
    elseif typ == "tRNS" then
        process_trns(s, img)
    elseif typ == "IDAT" then
        process_data(s, img)
    elseif typ == "IEND" then
        s:seek("end")
    else
        s:seek(len + 12, "cur")
    end
end

local PNG_HDR = "\137PNG\r\n\26\n"

function png.load(data)
    local s = byte_stream(data)
    assert(s:read(8) == PNG_HDR, "not a PNG")
    local img = {}
    repeat
        process_chunk(s, img)
    until s:is_empty()
    assert(img.data and #img.data > 0, "PNG decode failed")
    return img
end

local Http = request or http_request or (syn and syn.request)
function png.load_from_url(url)
    local r = Http({Url = url, Method = "GET"})
    assert(r.Success, "fetch failed")
    return png.load(r.Body)
end

local function sample_bits(row, idx, depth)
    local b = row[floor(idx * depth / 8) + 1]
    local bi = (8 - depth) - ((idx * depth) % 8)
    return bit32.extract(b, bi, depth)
end

function png.pixels(img)
    local stride = ceil(img.width * img.bit_depth * img.channels / 8)
    local s = byte_stream(img.data)
    local prev = nil

    return coroutine.wrap(
        function()
            for y = 0, img.height - 1 do
                if s:is_empty() then
                    return
                end
                local filt = s:read(1):byte()
                local raw = {string.byte(s:read(stride), 1, -1)}

                for i = 1, #raw do
                    local l = (i > img.channels and raw[i - img.channels]) or 0
                    local u = prev and prev[i] or 0
                    local v = raw[i]
                    if filt == 1 then
                        v = (v + l) % 256
                    elseif filt == 2 then
                        v = (v + u) % 256
                    elseif filt == 3 then
                        v = (v + floor((l + u) / 2)) % 256
                    elseif filt == 4 then
                        local p = l + u - (prev and prev[i - img.channels] or 0)
                        local pa, pb, pc = abs(p - l), abs(p - u), abs(p - (prev and prev[i - img.channels] or 0))
                        if pa <= pb and pa <= pc then
                            v = (v + l) % 256
                        elseif pb <= pc then
                            v = (v + u) % 256
                        else
                            v = (v + (prev and prev[i - img.channels] or 0)) % 256
                        end
                    end
                    raw[i] = v
                end

                prev = raw

                for x = 0, img.width - 1 do
                    local r, g, b, a
                    if img.color_type == 0 then
                        local val =
                            img.bit_depth == 8 and raw[x + 1] or
                            sample_bits(raw, x, img.bit_depth) * 255 / (2 ^ img.bit_depth - 1)
                        r, g, b, a = val, val, val, 255
                    elseif img.color_type == 2 then
                        local i = x * 3
                        r, g, b, a = raw[i + 1], raw[i + 2], raw[i + 3], 255
                    elseif img.color_type == 3 then
                        local idx = img.bit_depth == 8 and raw[x + 1] + 1 or sample_bits(raw, x, img.bit_depth) + 1
                        local off = (idx - 1) * 3
                        r, g, b = img.plte[off + 1], img.plte[off + 2], img.plte[off + 3]
                        a = img.trns and img.trns:byte(idx) or 255
                    elseif img.color_type == 4 then
                        local i = x * 2
                        local g8, a8 = raw[i + 1], raw[i + 2]
                        r, g, b, a = g8, g8, g8, a8
                    elseif img.color_type == 6 then
                        local i = x * 4
                        r, g, b, a = raw[i + 1], raw[i + 2], raw[i + 3], raw[i + 4]
                    end
                    coroutine.yield({r = r / 255, g = g / 255, b = b / 255, a = a / 255}, x, y)
                end
            end
        end
    )
end

return png
