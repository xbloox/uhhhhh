-- png.lua  •  universal PNG decoder (colour-types 0 2 3 4 6, bit-depths 1-8)

local png = {}

-- ─────────────────────────────────────────── helpers ────────────────────────
local floor, ceil, abs = math.floor, math.ceil, math.abs

-- big-endian byte-string → integer  (pass-through if already numeric)
local function int(bytes)
    if type(bytes) ~= "string" then
        return bytes
    end
    local n = 0
    for i = 1, #bytes do
        n = 256 * n + bytes:byte(i)
    end
    return n
end

-- number-or-byte-string → big-endian bit-string
local function bits(b, width)
    if type(b) == "number" then
        local num = b -- FIX: copy to local, never call nil
        local s = ""
        for _ = 1, width do
            s = (num % 2) .. s
            num = floor(num / 2)
        end
        return s
    else
        local out = {}
        for i = 1, #b do
            out[#out + 1] = bits(b:byte(i), 8)
        end
        return table.concat(out)
    end
end

-- minimal stand-in when bit32 lib is missing (some executors)
if not bit32 then
    bit32 = {}
    function bit32.extract(n, off, w)
        return floor(n / 2 ^ off) % 2 ^ w
    end
end

-- byte stream
local function byte_stream(raw)
    local pos = 0
    return {
        read = function(_, n)
            local s = raw:sub(pos + 1, pos + n)
            pos = pos + n
            return s
        end,
        seek = function(_, n, wh)
            if wh == "beg" then
                pos = n
            elseif wh == "end" then
                pos = #raw
            else
                pos = pos + n
            end
        end,
        is_empty = function()
            return pos >= #raw
        end
    }
end

-- bit stream
local function bit_stream(raw, off)
    local pos = 0
    off = off or 0
    return {
        read = function(_, n, rev)
            local start = floor(pos / 8) + off + 1
            local slice = raw:sub(start, start + ceil(n / 8))
            local b = bits(slice:byte(1, -1), 8 * #slice):sub(pos % 8 + 1, pos % 8 + n)
            pos = pos + n
            return rev and b or b:reverse()
        end,
        seek = function(_, n)
            if n == "beg" then
                pos = 0
            elseif n == "end" then
                pos = 8 * #raw
            else
                pos = pos + n
            end
        end,
        is_empty = function()
            return pos >= 8 * #raw
        end
    }
end

-- output buffer with back-copy (inflate)
local function output_stream()
    local buf, p = {}, 0
    local O = {}
    function O.write(_, s)
        for i = 1, #s do
            buf[#buf + 1] = s:sub(i, i)
        end
        p = p + #s
    end
    function O.back_copy(_, dist, len)
        local start = p - dist + 1
        local seg = {}
        for i = start, start + len - 1 do
            seg[#seg + 1] = buf[i]
        end
        local chunk = table.concat(seg)
        O.write(_, (chunk):rep(math.ceil(len / #chunk)):sub(1, len))
    end
    function O.raw()
        return table.concat(buf)
    end
    return O
end

-- ───────────────────────── Huffman helpers (canonical codes) ───────────────
local PT_W = 8
local function canonical_codes(lens)
    local pairs = {}
    for sym, L in ipairs(lens) do
        if L > 0 then
            pairs[#pairs + 1] = {L, sym - 1}
        end
    end
    table.sort(
        pairs,
        function(a, b)
            return a[1] == b[1] and a[2] < b[2] or a[1] < b[1]
        end
    )
    local codes, alpha, code = {}, {}, 0
    for i, pr in ipairs(pairs) do
        local L, sym = pr[1], pr[2]
        codes[i] = bits(code, L)
        alpha[i] = sym
        code = (code + 1) * 2 ^ ((pairs[i + 1] and pairs[i + 1][1] or L) - L)
    end
    return codes, alpha
end

local function prefix_table(codes, alpha)
    local T = {}
    for i, cd in ipairs(codes) do
        local unused = PT_W - #cd
        local entry = {value = alpha[i], unused = unused}
        if unused == 0 then
            T[cd] = entry
        else
            for n = 0, 2 ^ unused - 1 do
                T[cd .. bits(n, unused)] = entry
            end
        end
    end
    return T
end

local function decoder(stream, lens)
    local codes, alpha = canonical_codes(lens)
    local tbl = prefix_table(codes, alpha)
    return function()
        local e = tbl[stream:read(PT_W, true)]
        stream:seek(-e.unused)
        return e.value
    end
end

-- ─────────────────────────────────────── inflate (dynamic blocks only) ─────
local function extra_bits(s)
    return (s < 4 or s > 29) and 0 or floor((s - 2) / 2)
end

local function inflate(stream)
    local out = output_stream()
    repeat
        local final = stream:read(1):byte() & 1
        assert(stream:read(2) == "\2", "only dynamic Huffman")
        local hlit = tonumber(stream:read(5), 2) + 257
        local hdist = tonumber(stream:read(5), 2) + 1
        local hclen = tonumber(stream:read(4), 2) + 4

        local cl_lens = {}
        for i = 1, hclen do
            cl_lens[i] = tonumber(stream:read(3), 2)
        end
        local cl_dec = decoder(stream, cl_lens)

        local lit_lens, dst_lens = {}, {}
        for i = 1, hlit do
            lit_lens[i] = cl_dec(stream)
        end
        for i = 1, hdist do
            dst_lens[i] = cl_dec(stream)
        end

        local lit_dec = decoder(stream, lit_lens)
        local dst_dec = decoder(stream, dst_lens)

        while true do
            local sym = lit_dec(stream)
            if sym < 256 then
                out:write(string.char(sym))
            elseif sym == 256 then
                break
            else
                local len = (sym == 285 and 258) or (3 + sym - 257 + tonumber(stream:read(extra_bits(sym)), 2))
                local dsym = dst_dec(stream)
                local dist = 1 + tonumber(stream:read(extra_bits(dsym)), 2)
                out:back_copy(dist, len)
            end
        end
    until final == 1
    return out:raw()
end

-- ───────────────────────────────────────── PNG container ───────────────────
local CHANNELS = {[0] = 1, [2] = 3, [3] = 1, [4] = 2, [6] = 4}

local function load_png(raw)
    local s = byte_stream(raw)
    assert(s:read(8) == "\137PNG\r\n\26\n", "not PNG")

    local img, idat = {}, ""
    while true do
        local len = int(s:read(4))
        local typ = s:read(4)
        local data = s:read(len)
        s:read(4) -- CRC

        if typ == "IHDR" then
            img.width = int(data:sub(1, 4))
            img.height = int(data:sub(5, 8))
            img.bit_depth = data:byte(9)
            img.color_type = data:byte(10)
            img.channels = CHANNELS[img.color_type]
        elseif typ == "PLTE" then
            img.plte = {string.byte(data, 1, -1)}
        elseif typ == "tRNS" then
            img.trns = data
        elseif typ == "IDAT" then
            idat = idat .. data
        elseif typ == "IEND" then
            break
        end
    end
    assert(idat ~= "", "missing IDAT")
    img.data = inflate(bit_stream(idat, 2))
    return img
end

function png.load(data)
    return load_png(data)
end

local Http = request or http_request or (syn and syn.request)
function png.load_from_url(url)
    local r = Http({Url = url, Method = "GET"})
    assert(r.Success, "fetch failed")
    return png.load(r.Body)
end

-- ───────────────────────────── pixel generator ─────────────────────────────
local function sample(row, idx, depth)
    local byte = row[floor(idx * depth / 8) + 1]
    local ofs = 8 - depth - ((idx * depth) % 8)
    return bit32.extract(byte, ofs, depth)
end

function png.pixels(img)
    local stride = ceil(img.width * img.bit_depth * img.channels / 8)
    local s = byte_stream(img.data)
    local prev = nil
    return coroutine.wrap(
        function()
            for y = 0, img.height - 1 do
                local filt = s:read(1):byte()
                local row = {string.byte(s:read(stride), 1, -1)}
                for i = 1, #row do
                    local l = (i > img.channels and row[i - img.channels]) or 0
                    local u = prev and prev[i] or 0
                    local v = row[i]
                    if filt == 1 then
                        v = (v + l) % 256
                    elseif filt == 2 then
                        v = (v + u) % 256
                    elseif filt == 3 then
                        v = (v + floor((l + u) / 2)) % 256
                    elseif filt == 4 then
                        local p = l + u - (prev and prev[i - img.channels] or 0)
                        local pa = abs(p - l)
                        local pb = abs(p - u)
                        local pc = abs(p - (prev and prev[i - img.channels] or 0))
                        if pa <= pb and pa <= pc then
                            v = (v + l) % 256
                        elseif pb <= pc then
                            v = (v + u) % 256
                        else
                            v = (v + (prev and prev[i - img.channels] or 0)) % 256
                        end
                    end
                    row[i] = v
                end
                prev = row
                for x = 0, img.width - 1 do
                    local r, g, b, a
                    if img.color_type == 0 then
                        local val =
                            img.bit_depth == 8 and row[x + 1] or
                            sample(row, x, img.bit_depth) * 255 / (2 ^ img.bit_depth - 1)
                        r, g, b, a = val, val, val, 255
                    elseif img.color_type == 2 then
                        local i = x * 3
                        r, g, b, a = row[i + 1], row[i + 2], row[i + 3], 255
                    elseif img.color_type == 3 then
                        local idx = img.bit_depth == 8 and row[x + 1] + 1 or sample(row, x, img.bit_depth) + 1
                        local o = (idx - 1) * 3
                        r, g, b = img.plte[o + 1], img.plte[o + 2], img.plte[o + 3]
                        a = img.trns and img.trns:byte(idx) or 255
                    elseif img.color_type == 4 then
                        local i = x * 2
                        local g8, a8 = row[i + 1], row[i + 2]
                        r, g, b, a = g8, g8, g8, a8
                    elseif img.color_type == 6 then
                        local i = x * 4
                        r, g, b, a = row[i + 1], row[i + 2], row[i + 3], row[i + 4]
                    end
                    coroutine.yield({r = r / 255, g = g / 255, b = b / 255, a = a / 255}, x, y)
                end
            end
        end
    )
end

return png
