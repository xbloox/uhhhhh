local png = {}

-- math/local shortcuts
local floor, ceil, min, max, abs = math.floor, math.ceil, math.min, math.max, math.abs

-- memoize helper
local function memoize(f)
    local cache = {}
    return function(...)
        local key = table.concat({...}, "-")
        if not cache[key] then
            cache[key] = f(...)
        end
        return cache[key]
    end
end

-- convert big-endian byte-string to integer
local function int(bytes)
    local n = 0
    for i = 1, #bytes do
        n = 256 * n + bytes:sub(i, i):byte()
    end
    return n
end
int = memoize(int)

-- parse a binary string "010101" → number
local function bint(bits)
    return tonumber(bits, 2) or 0
end
bint = memoize(bint)

-- turn a number or string into an N-bit binary string
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
bits = memoize(bits)

-- repeat/stretch a short byte-string
local function fill(bytes, len)
    return bytes:rep(floor(len / #bytes)) .. bytes:sub(1, len % #bytes)
end

-- zip/unzip, map, filter, find, slice, range
local function zip(t1, t2)
    local out = {}
    for i = 1, max(#t1, #t2) do
        out[#out + 1] = {t1[i], t2[i]}
    end
    return out
end

local function unzip(z)
    local t1, t2 = {}, {}
    for i = 1, #z do
        t1[#t1 + 1], t2[#t2 + 1] = z[i][1], z[i][2]
    end
    return t1, t2
end

local function map(f, t)
    local out = {}
    for i = 1, #t do
        out[#out + 1] = f(t[i], i)
    end
    return out
end

local function filter(pred, t)
    local out = {}
    for i = 1, #t do
        if pred(t[i], i) then
            out[#out + 1] = t[i]
        end
    end
    return out
end

local function find(key, t)
    if type(key) == "function" then
        for i = 1, #t do
            if key(t[i]) then
                return i
            end
        end
        return nil
    else
        return find(
            function(x)
                return x == key
            end,
            t
        )
    end
end

local function slice(t, i, j, step)
    local out = {}
    local start = (i < 1 and 1) or i
    local finish = (j and j) or #t
    for k = start, finish, step or 1 do
        out[#out + 1] = t[k]
    end
    return out
end

local function range(i, j)
    local r = {}
    if j then
        for k = i, j do
            r[#r + 1] = k
        end
    else
        for k = 0, i - 1 do
            r[#r + 1] = k
        end
    end
    return r
end

-- simple byte stream
local function byte_stream(raw)
    local curr = 0
    return {
        read = function(_, n)
            local s = raw:sub(curr + 1, curr + n)
            curr = curr + n
            return s
        end,
        seek = function(_, n, whence)
            if whence == "beg" then
                curr = n
            elseif whence == "end" then
                curr = #raw
            else
                curr = curr + n
            end
            return nil
        end,
        is_empty = function()
            return curr >= #raw
        end,
        pos = function()
            return curr
        end,
        raw = function()
            return raw
        end
    }
end

-- bit‐level stream
local function bit_stream(raw, offset)
    local curr = 0
    offset = offset or 0
    return {
        read = function(_, n, reverse)
            local start = floor(curr / 8) + offset + 1
            local slice = raw:sub(start, start + ceil(n / 8))
            local b = bits(slice):sub(curr % 8 + 1, curr % 8 + n)
            curr = curr + n
            return reverse and b or b:reverse()
        end,
        seek = function(_, n)
            if n == "beg" then
                curr = 0
            elseif n == "end" then
                curr = 8 * #raw
            else
                curr = curr + n
            end
            return nil
        end,
        is_empty = function()
            return curr >= 8 * #raw
        end,
        pos = function()
            return curr
        end
    }
end

-- output buffer with backwards-copy support
local function output_stream()
    local buf, curr = {}, 0
    local S = {}
    function S.write(_, bytes)
        for i = 1, #bytes do
            buf[#buf + 1] = bytes:sub(i, i)
        end
        curr = curr + #bytes
    end
    function S.back_read(_, offset, n)
        local out = {}
        local start = curr - offset + 1
        for i = start, start + n - 1 do
            out[#out + 1] = buf[i]
        end
        return table.concat(out)
    end
    function S.back_copy(_, dist, len)
        local start = curr - dist + 1
        local copy = {}
        for i = start, start + len - 1 do
            copy[#copy + 1] = buf[i]
        end
        S.write(_, fill(table.concat(copy), len))
    end
    function S.pos()
        return curr
    end
    function S.raw()
        return table.concat(buf)
    end
    return S
end

-- constants for inflate
local CL_ORDER = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15}
local MAX_BITS = 15
local PT_W = 8

-- header: length bytes → list of code lengths
local function cl_code_lens(stream, hclen)
    local out = {}
    for i = 1, hclen do
        out[#out + 1] = bint(stream:read(3))
    end
    return out
end

-- build (length, symbol) pairs sorted by length then symbol
local function code_tree(lens, alpha)
    alpha = alpha or range(#lens)
    local zs =
        filter(
        function(z, i)
            return lens[i] and lens[i] > 0
        end,
        alpha
    )
    local ls =
        filter(
        function(x)
            return x > 0
        end,
        lens
    )
    local tree = zip(ls, zs)
    table.sort(
        tree,
        function(a, b)
            if a[1] == b[1] then
                return a[2] < b[2]
            end
            return a[1] < b[1]
        end
    )
    return unzip(tree)
end

-- produce canonical codes as bit-strings
local function codes(lens)
    local out, code = {}, 0
    for i = 1, #lens do
        out[#out + 1] = bits(code, lens[i])
        if i < #lens then
            code = (code + 1) * 2 ^ (lens[i + 1] - lens[i])
        end
    end
    return out
end

-- handle codes longer than PT_W bits
local function handle_long(codesList, alpha, pt)
    local idx =
        find(
        function(x)
            return #x > PT_W
        end,
        codesList
    )
    local long = slice(zip(codesList, alpha), idx)
    local done = 0
    while done < #long do
        local prefix = long[done + 1][1]:sub(1, PT_W)
        local same =
            filter(
            function(z)
                return z[1]:sub(1, PT_W) == prefix
            end,
            long
        )
        local tail =
            map(
            function(z)
                return {z[1]:sub(PT_W + 1), z[2]}
            end,
            same
        )
        pt[prefix] = {rest = prefix_table(unzip(tail)), unused = 0}
        done = done + #same
    end
end

-- build a prefix lookup table for lengths ≤ PT_W
function prefix_table(codesList, alpha)
    local pt = {}
    if #codesList[#codesList] > PT_W then
        handle_long(codesList, alpha, pt)
    end
    for i = 1, #codesList do
        local cd = codesList[i]
        if #cd > PT_W then
            break
        end
        local entry = {value = alpha[i], unused = PT_W - #cd}
        if entry.unused == 0 then
            pt[cd] = entry
        else
            for n = 0, 2 ^ entry.unused - 1 do
                pt[cd .. bits(n, entry.unused)] = entry
            end
        end
    end
    return pt
end

-- return a decoder(stream) → symbol
function huffman_decoder(lens, alpha)
    local base = prefix_table(codes(lens), alpha)
    return function(stream)
        local entry, tableRef = nil, base
        repeat
            entry = tableRef[stream:read(PT_W, true)]
            stream:seek(-entry.unused)
            tableRef = entry.rest
        until not tableRef
        return entry.value
    end
end

-- read code lengths from bitstream
local function code_lens(stream, decode, n)
    local out = {}
    while #out < n do
        local v = decode(stream)
        if v < 16 then
            out[#out + 1] = v
        elseif v == 16 then
            local cnt = bint(stream:read(2)) + 3
            for i = 1, cnt do
                out[#out + 1] = out[#out]
            end
        elseif v == 17 then
            local cnt = bint(stream:read(3)) + 3
            for i = 1, cnt do
                out[#out + 1] = 0
            end
        else
            local cnt = bint(stream:read(7)) + 11
            for i = 1, cnt do
                out[#out + 1] = 0
            end
        end
    end
    return out
end

-- build literal/length & distance decoders
local function code_trees(stream)
    local hlit = bint(stream:read(5)) + 257
    local hdist = bint(stream:read(5)) + 1
    local hclen = bint(stream:read(4)) + 4
    local cld = huffman_decoder(code_tree(cl_code_lens(stream, hclen), CL_ORDER))
    local ld = huffman_decoder(code_tree(code_lens(stream, cld, hlit)))
    local dd = huffman_decoder(code_tree(code_lens(stream, cld, hdist)))
    return ld, dd
end

-- extra bits based on symbol
local function extra_bits(sym)
    if sym < 4 or sym > 29 then
        return 0
    end
    if sym <= 29 then
        return floor((sym - 2) / 2)
    end
    return 0
end
extra_bits = memoize(extra_bits)

-- decode length for a symbol and extra bits
local function decode_len(sym, bitsStr)
    if sym < 257 or sym > 285 then
        error("len out of range")
    end
    if sym == 285 then
        return 258
    end
    local base = 3 + (sym - 257) * ((sym < 285) and 1 or 0)
    return base + bint(bitsStr)
end

-- decode distance
local function decode_dist(sym, bitsStr)
    return bint(bitsStr) + 1
end
decode_dist = memoize(decode_dist)

-- inflate DEFLATE blocks (only type 2 supported)
local function inflate(stream)
    local out = output_stream()
    repeat
        local bfinal = bint(stream:read(1))
        local btype = bint(stream:read(2))
        if btype ~= 2 then
            error("only dynamic Huffman supported")
        end
        local ld, dd = code_trees(stream)
        while true do
            local v = ld(stream)
            if v < 256 then
                out:write(string.char(v))
            elseif v == 256 then
                break
            else
                local len = decode_len(v, stream:read(extra_bits(v)))
                local dsym = dd(stream)
                local dist = decode_dist(dsym, stream:read(extra_bits(dsym)))
                out:back_copy(dist, len)
            end
        end
    until bfinal == 1
    return out
end

-- chunk processing

local CHANNELS = {[0] = 1, [2] = 3, [4] = 2, [6] = 4}

local function process_header(stream, image)
    stream:seek(8, "beg")
    image.width = int(stream:read(4))
    image.height = int(stream:read(4))
    image.bit_depth = int(stream:read(1))
    image.color_type = int(stream:read(1))
    image.channels = CHANNELS[image.color_type]
    stream:seek(5, "cur")
end

local function process_data(stream, image)
    local clen = int(stream:read(4))
    stream:seek(4, "cur") -- skip "IDAT"
    local zstream = output_stream()
    repeat
        zstream:write(stream:read(clen))
        stream:seek(4, "cur") -- skip CRC
        clen = int(stream:read(4))
    until stream:read(4) ~= "IDAT"
    stream:seek(-8, "cur")
    local bstr = bit_stream(zstream:raw(), 2)
    image.data = inflate(bstr)
end

local function process_chunk(stream, image)
    local clen = int(stream:read(4))
    local ctype = stream:read(4)
    stream:seek(-8, "cur")
    if ctype == "IHDR" then
        process_header(stream, image)
    elseif ctype == "IDAT" then
        process_data(stream, image)
    elseif ctype == "IEND" then
        stream:seek("end")
    else
        stream:seek(clen + 12, "cur")
    end
end

-- public loader from raw PNG bytes
local PNG_HDR = "\137PNG\r\n\26\n"
function png.load(data)
    local st = byte_stream(data)
    assert(st:read(8) == PNG_HDR, "not a PNG")
    local image = {}
    repeat
        process_chunk(st, image)
    until st:is_empty()
    return image
end

-- fetch via HTTP
local Http = request or http_request or (syn and syn.request)
function png.load_from_url(url)
    local res = Http({Url = url, Method = "GET"})
    assert(res.Success, "PNG fetch failed")
    return png.load(res.Body)
end

-- iterate pixels: returns p, x, y
function png.pixels(image)
    local idx = 0
    local next_line =
        (function()
        local scan = png._scan -- defined below
        return scan(image)
    end)()

    -- wrap scanlines iterator
    return function()
        local px, x, y = next_line()
        if not px then
            return nil
        end
        idx = idx + 1
        return px, x, y
    end
end

-- internal scanlines reader (unfiltered rows → one scanline at a time)
do
    local paeth = function(a, b, c)
        local p = a + b - c
        local pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
        if pa <= pb and pa <= pc then
            return a
        elseif pb <= pc then
            return b
        else
            return c
        end
    end

    png._scan = function(image)
        local w, h = image.width, image.height
        local stride = w * (image.bit_depth / 8) * image.channels
        local bs = byte_stream(image.data)

        local function gen_line()
            if bs:is_empty() then
                return nil
            end
            local filter = int(bs:read(1))
            local row = {string.byte(bs:read(stride), 1, -1)}
            -- unfilter
            for i = 1, #row do
                local left = (i > image.channels and row[i - image.channels]) or 0
                local up = (bs.pos and 0) -- we could store prev rows here if needed
                local val
                if filter == 0 then
                    val = row[i]
                elseif filter == 1 then
                    val = (row[i] + left) % 256
                elseif filter == 2 then
                    val = (row[i] + up) % 256
                elseif filter == 3 then
                    val = (row[i] + floor((left + up) / 2)) % 256
                elseif filter == 4 then
                    val = (row[i] + paeth(left, up, 0)) % 256
                end
                row[i] = val
            end
            return row
        end

        return coroutine.wrap(
            function()
                for y = 0, h - 1 do
                    local row = gen_line()
                    if not row then
                        return
                    end
                    local pxRow = {}
                    for x = 0, w - 1 do
                        local idx = x * image.channels
                        local entry = {r = row[idx + 1] / 255, g = row[idx + 2] / 255, b = row[idx + 3] / 255}
                        if image.channels == 4 then
                            entry.a = row[idx + 4] / 255
                        else
                            entry.a = 1
                        end
                        coroutine.yield(entry, x, y)
                    end
                end
            end
        )
    end
end

return png
