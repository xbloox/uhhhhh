local png = {}

local floor, ceil, abs = math.floor, math.ceil, math.abs

local function memo(f)
    local c = setmetatable({}, {__mode = "kv"})
    return function(...)
        local k = table.concat({...}, "-")
        if not c[k] then
            c[k] = f(...)
        end
        return c[k]
    end
end
local function int(b)
    local n = 0
    for i = 1, #b do
        n = 256 * n + b:sub(i, i):byte()
    end
    return n
end
int = memo(int)
local function bits(b, w)
    local s = ""
    if type(b) == "number" then
        for i = 1, w do
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
local function bint(x)
    return tonumber(x, 2) or 0
end
bint = memo(bint)
local function byte_stream(r)
    local c = 0
    return {read = function(_, n)
            local s = r:sub(c + 1, c + n)
            c = c + n
            return s
        end, seek = function(_, n, w)
            if w == "beg" then
                c = n
            elseif w == "end" then
                c = #r
            else
                c = c + n
            end
        end, is_empty = function()
            return c >= #r
        end, pos = function()
            return c
        end, raw = function()
            return r
        end}
end
local function bit_stream(r, o)
    local c = 0
    o = o or 0
    return {read = function(_, n, rev)
            local st = floor(c / 8) + o + 1
            local sl = r:sub(st, st + ceil(n / 8))
            local b = bits(sl):sub(c % 8 + 1, c % 8 + n)
            c = c + n
            return rev and b or b:reverse()
        end, seek = function(_, n)
            if n == "beg" then
                c = 0
            elseif n == "end" then
                c = 8 * #r
            else
                c = c + n
            end
        end, is_empty = function()
            return c >= 8 * #r
        end, pos = function()
            return c
        end}
end
local function output_stream()
    local b, cur = {}, 0
    local S = {}
    function S.write(_, s)
        for i = 1, #s do
            b[#b + 1] = s:sub(i, i)
        end
        cur = cur + #s
    end
    function S.back_copy(_, d, l)
        local st = cur - d + 1
        local cp = {}
        for i = st, st + l - 1 do
            cp[#cp + 1] = b[i]
        end
        S.write(_, string.rep(table.concat(cp), ceil(l / #cp)):sub(1, l))
    end
    function S.raw()
        return table.concat(b)
    end
    return S
end
local CHANNELS = {[0] = 1, [2] = 3, [3] = 1, [4] = 2, [6] = 4}
local PT_W = 8
local CL_ORDER = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15}
local function prefix_table(code, alpha)
    local pt = {}
    local function expand(cds, alp)
        local idx
        for i, v in ipairs(cds) do
            if #v > PT_W then
                idx = i
                break
            end
        end
        if not idx then
            return
        end
        local long = {}
        for i = idx, #cds do
            long[#long + 1] = {cds[i], alp[i]}
        end
        local done = 0
        while done < #long do
            local pre = long[done + 1][1]:sub(1, PT_W)
            local same = {}
            for _, z in ipairs(long) do
                if z[1]:sub(1, PT_W) == pre then
                    same[#same + 1] = z
                end
            end
            local tail = {}
            for _, z in ipairs(same) do
                tail[#tail + 1] = {z[1]:sub(PT_W + 1), z[2]}
            end
            pt[pre] = {
                rest = prefix_table(
                    (function(t)
                        local a = {}
                        for _, x in ipairs(t) do
                            a[#a + 1] = x[1]
                        end
                        return a
                    end)(tail),
                    (function(t)
                        local a = {}
                        for _, x in ipairs(t) do
                            a[#a + 1] = x[2]
                        end
                        return a
                    end)(tail)
                ),
                unused = 0
            }
            done = done + #same
        end
    end
    expand(code, alpha)
    for i, cd in ipairs(code) do
        if #cd > PT_W then
            break
        end
        local e = {value = alpha[i], unused = PT_W - #cd}
        if e.unused == 0 then
            pt[cd] = e
        else
            for n = 0, 2 ^ e.unused - 1 do
                pt[cd .. bits(n, e.unused)] = e
            end
        end
    end
    return pt
end
local function codes(len)
    local out, c = {}, 0
    for i = 1, #len do
        out[#out + 1] = bits(c, len[i])
        if i < #len then
            c = (c + 1) * 2 ^ (len[i + 1] - len[i])
        end
    end
    return out
end
local function code_tree(len, alpha)
    local zs, ls = {}, {}
    alpha = alpha or (function(n)
            local r = {}
            for i = 0, n - 1 do
                r[#r + 1] = i
            end
            return r
        end)(#len)
    for i, v in ipairs(alpha) do
        if len[i] and len[i] > 0 then
            zs[#zs + 1] = v
            ls[#ls + 1] = len[i]
        end
    end
    local t = {}
    for i = 1, #zs do
        t[#t + 1] = {ls[i], zs[i]}
    end
    table.sort(
        t,
        function(a, b)
            return a[1] == b[1] and a[2] < b[2] or a[1] < b[1]
        end
    )
    local l, z = {}, {}
    for _, v in ipairs(t) do
        l[#l + 1], z[#z + 1] = v[1], v[2]
    end
    return l, z
end
local function hdec(l, alpha)
    local base = prefix_table(codes(l), alpha)
    return function(st)
        local e, t = nil, base
        repeat
            e = t and t[st:read(PT_W, true)] or base[st:read(PT_W, true)]
            st:seek(-e.unused)
            t = e.rest
        until not t
        return e.value
    end
end
local function cl_lens(st, h)
    local o = {}
    for i = 1, h do
        o[#o + 1] = bint(st:read(3))
    end
    return o
end
local function code_lens(st, dec, n)
    local o = {}
    while #o < n do
        local v = dec(st)
        if v < 16 then
            o[#o + 1] = v
        elseif v == 16 then
            local c = bint(st:read(2)) + 3
            for _ = 1, c do
                o[#o + 1] = o[#o]
            end
        elseif v == 17 then
            local c = bint(st:read(3)) + 3
            for _ = 1, c do
                o[#o + 1] = 0
            end
        else
            local c = bint(st:read(7)) + 11
            for _ = 1, c do
                o[#o + 1] = 0
            end
        end
    end
    return o
end
local function extra_bits(s)
    if s < 4 or s > 29 then
        return 0
    end
    return floor((s - 2) / 2)
end
extra_bits = memo(extra_bits)
local function decode_len(s, b)
    return s == 285 and 258 or 3 + (s - 257) + bint(b)
end
local function decode_dist(s, b)
    return bint(b) + 1
end
decode_dist = memo(decode_dist)
local function inflate(st)
    local out = output_stream()
    repeat
        local bfinal = bint(st:read(1))
        local btype = bint(st:read(2))
        if btype ~= 2 then
            error("only dynamic")
        end
        local hlit = bint(st:read(5)) + 257
        local hdist = bint(st:read(5)) + 1
        local hclen = bint(st:read(4)) + 4
        local cld =
            hdec(
            (function(st, h)
                local o = {}
                for i = 1, h do
                    o[#o + 1] = bint(st:read(3))
                end
                return code_tree(o, CL_ORDER)
            end)(st, hclen)
        )
        local ld = hdec(code_tree(code_lens(st, cld, hlit)))
        local dd = hdec(code_tree(code_lens(st, cld, hdist)))
        while true do
            local v = ld(st)
            if v < 256 then
                out:write(string.char(v))
            elseif v == 256 then
                break
            else
                local len = decode_len(v, st:read(extra_bits(v)))
                local ds = dd(st)
                local dist = decode_dist(ds, st:read(extra_bits(ds)))
                out:back_copy(dist, len)
            end
        end
    until bfinal == 1
    return out
end
local function process_header(st, img)
    st:seek(8, "beg")
    img.width = int(st:read(4))
    img.height = int(st:read(4))
    img.bit_depth = int(st:read(1))
    img.color_type = int(st:read(1))
    img.channels = CHANNELS[img.color_type]
    st:seek(5, "cur")
end
local function process_palette(st, img)
    local len = int(st:read(4))
    st:seek(4, "cur")
    img.plte = {string.byte(st:read(len), 1, -1)}
    st:seek(4, "cur")
end
local function process_trns(st, img)
    local len = int(st:read(4))
    st:seek(4, "cur")
    img.trns = st:read(len)
    st:seek(4, "cur")
end
local function process_data(st, img)
    local len = int(st:read(4))
    st:seek(4, "cur")
    local zb = output_stream()
    repeat
        zb:write(st:read(len))
        st:seek(4, "cur")
        len = int(st:read(4))
    until st:read(4) ~= "IDAT"
    st:seek(-8, "cur")
    img.data = inflate(bit_stream(zb:raw(), 2)):raw()
end
local function process_chunk(st, img)
    local len = int(st:read(4))
    local typ = st:read(4)
    st:seek(-8, "cur")
    if typ == "IHDR" then
        process_header(st, img)
    elseif typ == "PLTE" then
        process_palette(st, img)
    elseif typ == "tRNS" then
        process_trns(st, img)
    elseif typ == "IDAT" then
        process_data(st, img)
    elseif typ == "IEND" then
        st:seek("end")
    else
        st:seek(len + 12, "cur")
    end
end
local PNG_HDR = "\137PNG\r\n\26\n"
function png.load(d)
    local st = byte_stream(d)
    assert(st:read(8) == PNG_HDR, "not png")
    local img = {}
    repeat
        process_chunk(st, img)
    until st:is_empty()
    assert(img.data and #img.data > 0, "decode failed")
    return img
end
local Http = request or http_request or (syn and syn.request)
function png.load_from_url(u)
    local r = Http({Url = u, Method = "GET"})
    assert(r.Success, "fetch failed")
    return png.load(r.Body)
end
local function sample(row, idx, depth)
    local b = row[floor(idx * depth / 8) + 1]
    local bit_idx = (8 - depth) - ((idx * depth) % 8)
    return bit32.extract(b, bit_idx, depth)
end
function png.pixels(img)
    local stride = ceil(img.width * img.bit_depth * img.channels / 8)
    local st = byte_stream(img.data)
    local prev = nil
    return coroutine.wrap(
        function()
            for y = 0, img.height - 1 do
                local filt = st:read(1):byte()
                local row = {string.byte(st:read(stride), 1, -1)}
                local function un(row)
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
                            local p = a + b - c
                            local pa, pb, pc =
                                abs(p - l),
                                abs(p - u),
                                abs(p - (l + u - (prev and prev[i - img.channels] or 0)))
                            if pa <= pb and pa <= pc then
                                v = (v + l) % 256
                            elseif pb <= pc then
                                v = (v + u) % 256
                            else
                                v = (v + (l + u - (prev and prev[i - img.channels] or 0))) % 256
                            end
                        end
                        row[i] = v
                    end
                    return row
                end
                row = un(row)
                prev = row
                for x = 0, img.width - 1 do
                    local r, g, b, a
                    if img.color_type == 0 then
                        local v =
                            img.bit_depth == 8 and row[x + 1] or
                            sample(row, x, img.bit_depth) * 255 / (2 ^ img.bit_depth - 1)
                        r, g, b = v, v, v
                        a = 255
                    elseif img.color_type == 2 then
                        local i = x * 3
                        r, g, b = row[i + 1], row[i + 2], row[i + 3]
                        a = 255
                    elseif img.color_type == 3 then
                        local idx = img.bit_depth == 8 and row[x + 1] + 1 or sample(row, x, img.bit_depth) + 1
                        local off = (idx - 1) * 3
                        r, g, b = img.plte[off + 1], img.plte[off + 2], img.plte[off + 3]
                        a = img.trns and img.trns:byte(idx) or 255
                    elseif img.color_type == 4 then
                        local i = x * 2
                        local g8 = row[i + 1]
                        local a8 = row[i + 2]
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
