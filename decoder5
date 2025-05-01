local png = {}

local floor, ceil, abs = math.floor, math.ceil, math.abs

local function memo(f)
    local cache = setmetatable({}, {__mode="kv"})
    return function(...)
        local key = table.concat({...}, "-")
        if not cache[key] then
            cache[key] = f(...)
        end
        return cache[key]
    end
end

local function int(b)
    local n = 0
    for i = 1, #b do
        n = 256*n + b:sub(i,i):byte()
    end
    return n
end
int = memo(int)

local function bits(b, w)
    local s = ""
    if type(b)=="number" then
        for i=1,w do s=(b%2)..s; b=floor(b/2) end
    else
        for i=1,#b do
            s = s .. bits(b:sub(i,i):byte(), 8):reverse()
        end
    end
    return s
end
bits = memo(bits)

local function bint(str)
    return tonumber(str,2) or 0
end
bint = memo(bint)

local function byte_stream(raw)
    local pos = 0
    return {
        read = function(_,n)
            local c = raw:sub(pos+1, pos+n)
            pos += n
            return c
        end,
        seek = function(_,n,whence)
            if whence=="beg" then pos=n
            elseif whence=="end" then pos=#raw
            else pos+=n end
        end,
        is_empty = function() return pos>=#raw end,
    }
end

local function bit_stream(raw, offset)
    local pos = 0; offset = offset or 0
    return {
        read = function(_,n,rev)
            local start = floor(pos/8)+offset+1
            local slice = raw:sub(start, start+ceil(n/8))
            local b = bits(slice):sub(pos%8+1, pos%8+n)
            pos += n
            return rev and b or b:reverse()
        end,
        seek = function(_,n)
            if n=="beg" then pos=0
            elseif n=="end" then pos=8*#raw
            else pos+=n end
        end,
        is_empty = function() return pos>=8*#raw end,
    }
end

local function output_stream()
    local buf, p = {}, 0
    local S = {}
    function S.write(_,s)
        for i=1,#s do buf[#buf+1] = s:sub(i,i) end
        p += #s
    end
    function S.back_copy(_,d,l)
        local st = p-d+1
        local seg = {}
        for i=st,st+l-1 do seg[#seg+1]=buf[i] end
        local s = table.concat(seg)
        local r = math.ceil(l/#s)
        S.write(_, s:rep(r):sub(1,l))
    end
    function S.raw() return table.concat(buf) end
    return S
end

local CHANNELS = {[0]=1,[2]=3,[3]=1,[4]=2,[6]=4}
local PT_W      = 8
local CL_ORDER  = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15}

local function prefix_table(codes, alpha)
    local pt = {}
    for i,cd in ipairs(codes) do
        if #cd > PT_W then
            local group = {}
            for j=i,#codes do group[#group+1]={codes[j],alpha[j]} end
            local done = 0
            while done < #group do
                local pre = group[done+1][1]:sub(1,PT_W)
                local same = {}
                for _,p in ipairs(group) do
                    if p[1]:sub(1,PT_W)==pre then same[#same+1]=p end
                end
                local tc, ta = {},{}
                for _,p in ipairs(same) do
                    tc[#tc+1] = p[1]:sub(PT_W+1)
                    ta[#ta+1] = p[2]
                end
                pt[pre] = {rest=prefix_table(tc,ta), unused=0}
                done += #same
            end
            break
        end
    end
    local code = 0
    for i,len in ipairs(codes) do
        local entry = {value=alpha[i], unused=PT_W-len}
        local bs    = bits(code,len)
        if entry.unused==0 then
            pt[bs] = entry
        else
            for n=0,2^entry.unused-1 do
                pt[bs..bits(n,entry.unused)] = entry
            end
        end
        if i<#codes then
            code = (code+1)*2^(codes[i+1]-codes[i])
        end
    end
    return pt
end

local function build_huffman(stream, lens, alpha)
    local table = prefix_table(lens, alpha)
    return function()
        local e = table[stream:read(PT_W, true)]
        stream:seek(-e.unused)
        while e.rest do
            local ne = e.rest[stream:read(PT_W,true)]
            stream:seek(-ne.unused)
            e = ne
        end
        return e.value
    end
end

local function decode_lengths(stream, count, dec)
    local out = {}
    while #out < count do
        local v = dec(stream)
        if v < 16 then
            out[#out+1] = v
        elseif v == 16 then
            local r = bint(stream:read(2)) + 3
            for _=1,r do out[#out+1] = out[#out] end
        elseif v == 17 then
            local r = bint(stream:read(3)) + 3
            for _=1,r do out[#out+1] = 0 end
        else
            local r = bint(stream:read(7)) + 11
            for _=1,r do out[#out+1] = 0 end
        end
    end
    return out
end

local function inflate(stream)
    local out = output_stream()
    while true do
        local final = bint(stream:read(1))
        local bt    = bint(stream:read(2))
        if bt~=2 then error("only dynamic Huffman") end
        local hlit = bint(stream:read(5))+257
        local hdist= bint(stream:read(5))+1
        local hclen= bint(stream:read(4))+4

        local cl_lens = {}
        for i=1,hclen do cl_lens[#cl_lens+1]=bint(stream:read(3)) end
        local cl_dec  = build_huffman(stream, cl_lens, CL_ORDER)

        local lit_lens = decode_lengths(stream, hlit,  cl_dec)
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
                local length = (sym==285 and 258)
                              or (3 + sym - 257 + bint(stream:read((sym<4 or sym>29) and 0 or floor((sym-2)/2))))
                local dist   = dst_dec(stream)
                local d      = bint(stream:read((dist<4 or dist>29) and 0 or floor((dist-2)/2))) + 1
                out:back_copy(d, length)
            end
        end

        if final==1 then break end
    end
    return out:raw()
end

local function load_png(raw)
    local s    = byte_stream(raw)
    local hdr  = s:read(8)
    assert(hdr=="\137PNG\r\n\26\n","not PNG")
    local img  = {}
    local idat = ""

    while true do
        local length = int(s:read(4))
        local ctype  = s:read(4)
        local data   = s:read(length)
        s:read(4)  

        if ctype=="IHDR" then
            img.width      = int(data:sub(1,4))
            img.height     = int(data:sub(5,8))
            img.bit_depth  = data:sub(9,9):byte()
            img.color_type = data:sub(10,10):byte()
            img.channels   = CHANNELS[img.color_type]
        elseif ctype=="PLTE" then
            img.plte = {string.byte(data,1,-1)}
        elseif ctype=="tRNS" then
            img.trns = data
        elseif ctype=="IDAT" then
            idat = idat..data
        elseif ctype=="IEND" then
            break
        end
    end

    assert(idat~="","no IDAT")
    img.data = inflate(bit_stream(idat,2))
    return img
end

function png.load(data)
    return load_png(data)
end

local Http = request or http_request or (syn and syn.request)

function png.load_from_url(url)
    local r = Http({Url=url, Method="GET"})
    assert(r and r.Success, "fetch failed")
    return png.load(r.Body)
end

local function sample_bits(row, idx, depth)
    local b  = row[floor(idx*depth/8)+1]
    local bi = (8-depth)-((idx*depth)%8)
    return bit32.extract(b, bi, depth)
end

function png.pixels(img)
    local stride = ceil(img.width * img.bit_depth * img.channels / 8)
    local s      = byte_stream(img.data)
    local prev   = nil

    return coroutine.wrap(function()
        for y=0,img.height-1 do
            if s:is_empty() then return end
            local filt = s:read(1):byte()
            local row  = {string.byte(s:read(stride),1,-1)}

            for i=1,#row do
                local l = (i>img.channels and row[i-img.channels]) or 0
                local u = prev and prev[i] or 0
                local v = row[i]
                if filt==1 then v=(v+l)%256
                elseif filt==2 then v=(v+u)%256
                elseif filt==3 then v=(v+floor((l+u)/2))%256
                elseif filt==4 then
                    local p = l+u - (prev and prev[i-img.channels] or 0)
                    local pa,pb,pc = abs(p-l),abs(p-u),abs(p-(prev and prev[i-img.channels] or 0))
                    if pa<=pb and pa<=pc then v=(v+l)%256
                    elseif pb<=pc then v=(v+u)%256
                    else v=(v+(prev and prev[i-img.channels] or 0))%256 end
                end
                row[i] = v
            end

            prev = row

            for x=0,img.width-1 do
                local r,g,b,a
                if img.color_type==0 then
                    local val = img.bit_depth==8 and row[x+1]
                              or sample_bits(row, x, img.bit_depth)*255/(2^img.bit_depth-1)
                    r,g,b,a = val,val,val,255

                elseif img.color_type==2 then
                    local i = x*3
                    r,g,b,a = row[i+1],row[i+2],row[i+3],255

                elseif img.color_type==3 then
                    local idx = img.bit_depth==8 and row[x+1]+1
                                or sample_bits(row, x, img.bit_depth)+1
                    local off = (idx-1)*3
                    r,g,b = img.plte[off+1], img.plte[off+2], img.plte[off+3]
                    a     = img.trns and img.trns:byte(idx) or 255

                elseif img.color_type==4 then
                    local i = x*2
                    local g8,a8 = row[i+1], row[i+2]
                    r,g,b,a = g8, g8, g8, a8

                elseif img.color_type==6 then
                    local i = x*4
                    r,g,b,a = row[i+1],row[i+2],row[i+3],row[i+4]
                end

                coroutine.yield({r=r/255,g=g/255,b=b/255,a=a/255}, x, y)
            end
        end
    end)
end

return png
