--[[
Copyright (c) 2017, Rosalie Petra barones van der Feltz

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright notice,
  this list of conditions and the following disclaimer in the documentation
  and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--]]
--[[
=================================== Manual ====================================
LuaData is a module for encoding Lua strings, booleans, numbers, and tables in
a plaintext format, with options for encryption.

-- How to use:
LuaData = require(path.to.LuaData) -- Requires the module

-- API:
variant           LuaData.Decode(string data, table external_values = nil, variant crypt_key = nil)
string [, number] LuaData.Encode(variant value, array external_values = nil, variant crypt_key = nil, boolean omit_unsupported_values = false)
variant           LuaData.BytesToValue(array data, table external_values = nil)
array [, number]  LuaData.ValueToBytes(variant value, array external_values = nil, boolean omit_unsupported_values = false)
array             LuaData.R85ToBytes(string r85_str)
string            LuaData.BytesToR85(array bytes)
string            LuaData.BytesToString(array bytes, number start_index = 1, number end_index = #bytes)
array             LuaData.StringToBytes(string str, table destination = nil)
array             LuaData.DecryptBytes(array bytes, variant crypt_key)
array             LuaData.EncryptBytes(array bytes, variant crypt_key)
string            LuaData.DecryptString(string cipher, variant crypt_key)
string            LuaData.EncryptString(string plaintext, variant crypt_key)

-- Notes:
1. LuaData.Decode and LuaData.Encode use R85 (radix 85) encoding to convert
  between bytes and string-safe text.
2. Values that are in the list 'external_values' will be encoded as a
  reference, then subtituted when decoding. The same values should be used when
  encoding and decoding.
3. The 'external_values' parameter can have a member called 'n' when decoding,
  indicating the number of values it contains. This can be used to substitue
  external values with nil values when decoding.
4. 'crypt_key' can be either a string, or an array of bytes.
5. If 'omit_unsupported_values' is true, then encoding functions don't error
  when encountering a value with an unsupported data type, and instead encoding
  functions return the number of values omitted as the second value.
6. LuaData.StringToBytes creates and returns a new table is a second arguments
  isn't provided.
7. LuaData.DecryptBytes and LuaData.EncryptBytes encrypt/decrypt the table that
 is passed as the first argument, modifying it, and also returns it.
--]]
 
local LuaData = {}

local dbgtraceback, error, frexp, next, strbyte, strchar, strformat, tblconcat, tblsort, tostring, type, xpcall = debug.traceback, error, math.frexp, next, string.byte, string.char, string.format, table.concat, table.sort, tostring, type, xpcall
local MATH_INF, MATH_NAN = math.huge, 0 / 0

local function CheckErrorLevel(error_level)
	if error_level == nil then
		return 2
	elseif type(error_level) ~= "number" then
		error("error level must be a number or nil", 3)
	end
	return error_level + 1
end

local function BytesToString(bytes, start_index, end_index)
	local buffer = {}
	start_index = start_index or 1
	end_index = end_index or #bytes
	for i = 0, end_index - start_index do
		buffer[i + 1] = strchar(bytes[start_index + i])
	end
	return tblconcat(buffer)
end
local function StringToBytes(str, dest)
	dest = dest or {}
	local dest_n = #dest
	for i = 1, #str, 4 do
		local dest_i = dest_n + i
		dest[dest_i], dest[dest_i + 1], dest[dest_i + 2], dest[dest_i + 3] = strbyte(str, i, i + 3)
	end
	return dest
end

local BYTECOUNT_THRESHOLDS = {0xFF, 0x100FF, 0x100FFFF, 4311744511} -- 4311744511 = 0x100FFFFFF
local function BytesNeededForReference(reference_id)
	if reference_id < 227 then
		return 1
	else
		reference_id = reference_id - 227
		for i = 1, 4 do
			if reference_id <= BYTECOUNT_THRESHOLDS[i] then
				return i + 1
			end
		end
		return MATH_INF
	end
end

-- Decoding functions
local DecodeHeader, DecodeValue
local DATA_DECODERS = {}

local LOOKUP_BYTE_MULTIPLIER = {1, 0x100, 0x10000, 0x1000000}
local LOOKUP_EXTENDED_OFFSET = {0, 0x10000, 0x1000000, 4294967296} -- 0x100000000

function DecodeHeader(state)
	local data, index = state.data, state.index
	local type_byte = data[index]
	local type_id, header_value
	if type_byte < 24 then
		local num_header_bytes = type_byte % 4
		type_id = (type_byte - num_header_bytes) * 0.25
		num_header_bytes = num_header_bytes + 1
		header_value = 0
		for i = 1, num_header_bytes do
			header_value = header_value + data[index + i] * LOOKUP_BYTE_MULTIPLIER[i]
		end
		if data[index + num_header_bytes] == 0 then
			header_value = header_value + LOOKUP_EXTENDED_OFFSET[num_header_bytes] -- make full use of values that can be represented with less bytes
		end
		if type_id == 0 then
			header_value = header_value + 227 -- no overlap with 0-header references
		end
		if type_id == 5 then
			type_id = 4
			header_value = -header_value
		end
		state.index = index + 1 + num_header_bytes
	else
		if type_byte >= 29 then
			type_id, header_value = 0, type_byte - 29
		elseif type_byte == 24 then
			type_id = 5
		elseif type_byte == 25 then
			type_id = 6
		elseif type_byte < 28 then
			type_id, header_value = 4, type_byte == 26
		elseif type_byte == 28 then
			type_id, header_value = 4, MATH_NAN
		end
		state.index = index + 1
	end
	return type_id, header_value
end

DATA_DECODERS[1] = function(state, num_pairs) -- key-value pair table
	local new_table = {}
	local entries, entry_id = state.entries, state.num_entries + 1
	entries[entry_id], state.num_entries = new_table, entry_id
	for i = 1, num_pairs do
		local key, value = DecodeValue(state), DecodeValue(state)
		if key ~= nil then
			new_table[key] = value
		end
	end
	return new_table
end
DATA_DECODERS[2] = function(state, num_values) -- array table (only natural numbers as keys)
	local new_table = {}
	local entries, entry_id = state.entries, state.num_entries + 1
	entries[entry_id], state.num_entries = new_table, entry_id
	for i = 1, num_values do
		new_table[i] = DecodeValue(state)
	end
	return new_table
end
DATA_DECODERS[3] = function(state, length)
	local data, index = state.data, state.index
	state.index = index + length
	return BytesToString(data, index, index + length - 1)
end
DATA_DECODERS[4] = function(state, value)
	return value
end
DATA_DECODERS[5] = function(state) -- float (4 bytes)
	local data, index = state.data, state.index
	state.index = index + 4
	local b2, b3 = data[index + 2], data[index + 3]
	local sign = b3 < 0x80 and 1 or -1
	local fraction = b2 % 0x80
	local exponent = b3 % 0x80 * 2 + (b2 - fraction) * 0.0078125
	fraction = (fraction * 0x100 + data[index + 1]) * 0x100 + data[index]
	if exponent == 0xFF then
		return sign * MATH_INF
	elseif exponent == 0 then
		return sign * fraction * 1.401298464324817e-45
	else
		return sign * (1 + fraction * 1.1920928955078125e-7) * 2 ^ (exponent - 127)
	end
end
DATA_DECODERS[6] = function(state) -- double (8 bytes)
	local data, index = state.data, state.index
	state.index = index + 8
	local b6, b7 = data[index + 6], data[index + 7]
	local sign = b7 < 0x80 and 1 or -1
	local fraction = b6 % 0x10
	local exponent = b7 % 0x80 * 0x10 + (b6 - fraction) * 0.0625
	fraction = (((((fraction * 0x100 + data[index + 5]) * 0x100 + data[index + 4]) * 0x100 + data[index + 3]) * 0x100 + data[index + 2]) * 0x100 + data[index + 1]) * 0x100 + data[index]
	-- infinity isn't represented, since it will be stored using float32
	if exponent == 0 then
		return sign * fraction * 5e-324 -- 5e-324 is smallest possible float
	else
		return sign * (1 + fraction * 2.220446049250313e-16) * 2 ^ (exponent - 1023)
	end
end

function DecodeValue(state)
	local entries = state.entries
	local bytes_used = state.index
	local type_id, header_value = DecodeHeader(state)
	if type_id == 0 then
		return entries[header_value + 1]
	else
		local value = DATA_DECODERS[type_id](state, header_value)
		bytes_used = state.index - bytes_used
		local num_entries = state.num_entries
		if type_id > 2 and bytes_used > BytesNeededForReference(num_entries) then -- tables are mapped while being decoded
			entries[num_entries + 1], state.num_entries = value, num_entries + 1
		end
		return value
	end
end

-- Encoding functions
local EncodeHeader, EncodeValue
local DATA_ENCODERS = {}

local function CreateEncodeState()
	return {buffer = {}, entries = {}, num_entries = 0}
end

function EncodeHeader(state, value, type_id, error_level, min_num_bytes)
	local buffer = state.buffer
	local buffer_n = #buffer + 1
	if type_id == 0 and value < 227 then
		buffer[buffer_n] = value + 29
	else
		if type_id == 0 then
			value = value - 227
		end
		if value > 4311744511 then -- 0x100FFFFFF
			error("the data cannot be encoded because it is too big", error_level + 1)
		else
			if not min_num_bytes then
				min_num_bytes = 4
				for i = 1, 3 do
					if value <= BYTECOUNT_THRESHOLDS[i] then
						min_num_bytes = i
						break
					end
				end
			end
			local extended_offset = LOOKUP_EXTENDED_OFFSET[min_num_bytes]
			if value >= extended_offset then
				value = value - extended_offset
			end
			local num_bytes, cutoff = 0, 1
			buffer[buffer_n] = 0
			repeat
				local byte = value / cutoff
				num_bytes, cutoff = num_bytes + 1, cutoff * 0x100
				buffer[buffer_n + num_bytes] = byte % 0x100 - byte % 1
			until cutoff > value and num_bytes >= min_num_bytes
			buffer[buffer_n] = type_id * 4 + num_bytes - 1
		end
	end
end

function DATA_ENCODERS.table(state, value, error_level)
	error_level = error_level + 1
	local keys, values, num_pairs = {}, {}, 0
	local array_n, is_dictionary = #value, false
	local num_values_omitted, extra_omitted = state.num_values_omitted, 0
	for key, value in next, value do
		local key_type = type(key)
		if not num_values_omitted or (DATA_ENCODERS[key_type] and DATA_ENCODERS[type(value)]) then
			num_pairs = num_pairs + 1
			keys[num_pairs], values[num_pairs] = key, value
			if key_type ~= "number" or key % 1 ~= 0 or key < 1 or key > array_n then
				is_dictionary = true
			end
		else
			extra_omitted = extra_omitted + 1
		end
	end
	is_dictionary = is_dictionary or (num_pairs + extra_omitted) ~= array_n
	if num_values_omitted then
		state.num_values_omitted = num_values_omitted + extra_omitted * (is_dictionary and 2 or 1)
	end
	EncodeHeader(state, num_pairs, is_dictionary and 1 or 2, error_level)
	for i = 1, num_pairs do
		if is_dictionary then
			EncodeValue(state, keys[i], error_level)
			EncodeValue(state, values[i], error_level)
		else
			EncodeValue(state, value[i], error_level)
		end
	end
end
function DATA_ENCODERS.string(state, value, error_level)
	EncodeHeader(state, #value, 3, error_level + 1)
	StringToBytes(value, state.buffer)
end
local function EncodeFloat32(state, value)
	local buffer = state.buffer
	local buffer_i = #buffer + 2
	buffer[buffer_i - 1] = 24
	local signed_bit = 0
	if value < 0 then
		signed_bit = 0x80
		value = -value
	end
	if value == MATH_INF then
		buffer[buffer_i], buffer[buffer_i + 1], buffer[buffer_i + 2], buffer[buffer_i + 3] = 0, 0, 0x80, signed_bit + 0x7F
	else
		local fraction, exponent = frexp(value)
		if exponent < -125 then -- subnormal
			fraction = value * 7.1362384635297994e+44
			exponent = 0
		else
			fraction = (fraction + fraction - 1) * 8388608
			exponent = exponent + 126
		end
		if exponent > 0xFE or fraction % 1 ~= 0 then
			return false -- use double precision float instead
		end
		local bi
		for i = 0, 2 do
			bi = fraction % 0x100
			fraction = (fraction - bi) * 0.00390625
			buffer[buffer_i + i] = bi
		end
		local exp_low = exponent % 2
		buffer[buffer_i + 2] = bi + exp_low * 0x80
		buffer[buffer_i + 3] = signed_bit + (exponent - exp_low) * 0.5
	end
	return true
end
function DATA_ENCODERS.number(state, value)
	local buffer = state.buffer
	local buffer_i = #buffer + 1
	if value ~= value then
		buffer[buffer_i] = 27 -- NaN
	elseif value >= -4311744511 and value <= 4311744511 and value % 1 == 0 then
		local type_id = 4
		if 1 / value < 0 then
			value = -value
			type_id = 5
		end
		EncodeHeader(state, value, type_id)
	elseif not EncodeFloat32(state, value) then
		for i = buffer_i, #buffer do
			buffer[i] = nil
		end
		buffer[buffer_i], buffer_i = 25, buffer_i + 1
		local signed_bit = 0
		if value < 0 then
			signed_bit = 0x80
			value = -value
		end
		local fraction, exponent = frexp(value)
		if exponent < -1021 then -- subnormal
			fraction = value * 8.98846567431158e+307 * 2251799813685248
			exponent = 0
		else
			fraction = (fraction + fraction - 1) * 4503599627370496 -- lowest 52 bits
			exponent = exponent + 1022 -- doubled the fraction so reduce exponent by 1, then add 1023 as the offset for storage
		end
		local bi
		for i = 0, 6 do
			bi = fraction % 0x100
			fraction = (fraction - bi) * 0.00390625
			buffer[buffer_i + i] = bi
		end
		local exp_low = exponent % 0x10
		buffer[buffer_i + 6] = bi + exp_low * 0x10
		buffer[buffer_i + 7] = signed_bit + (exponent - exp_low) * 0.0625
	end
end
function DATA_ENCODERS.boolean(state, value)
	local buffer = state.buffer
	buffer[#buffer + 1] = value and 26 or 27
end

function EncodeValue(state, value, error_level)
	error_level = error_level + 1
	local entries = state.entries
	local entry_id = entries[value]
	if entry_id then
		EncodeHeader(state, entry_id, 0, error_level)
	else
		local value_type = type(value)
		local encoder = DATA_ENCODERS[value_type]
		if encoder then
			local num_entries = state.num_entries
			if value_type == "table" then -- reference tables beforehand to deal with cyclic tables
				entries[value], state.num_entries = num_entries, num_entries + 1
			end
			local buffer = state.buffer
			local bytes_used = #buffer
			encoder(state, value, error_level)
			bytes_used = #buffer - bytes_used
			if value_type ~= "table" and bytes_used > BytesNeededForReference(num_entries) then
				entries[value], state.num_entries = num_entries, num_entries + 1
			end
		else
			local num_values_omitted = state.num_values_omitted
			if not num_values_omitted then
				error("attempt to encode unsupported data type '" .. typeof(value) .. "' (" .. tostring(value) .. ")", error_level)
			end
			state.num_values_omitted = num_values_omitted + 1
		end
	end
end

local function HandleDecodeError(error_message)
	local trace = dbgtraceback()
	local end_line = trace:find("\n[^\n]*xpcall") or trace:find("\n[^\n]*BytesToValue") or (#trace + 1)
	return "(error: " .. error_message .. ")\n" .. trace:sub(1, end_line - 1)
end
local function BytesToValue(bytes, external_values, error_level)
	if #bytes == 0 then
		return nil
	end
	error_level = CheckErrorLevel(error_level)
	if type(bytes) ~= "table" then
		error("argument #1 to BytesToValue must be a table", error_level)
	end
	if external_values ~= nil and type(external_values) ~= "table" then
		error("argument #2 to BytesToValue must be a table or nil", error_level)
	end
	local entries = {}
	local state = {data = bytes, index = 1, entries = entries, num_entries = 0}
	if external_values then
		local num_entries = external_values.n or #external_values
		for i = 1, num_entries do
			entries[i] = external_values[i]
		end
		state.num_entries = num_entries
	end
	local success, result = xpcall(function() return DecodeValue(state) end, HandleDecodeError)
	if not success then
		error("the data is corrupt and could not be decoded " .. result, error_level)
	end
	if state.index ~= #state.data + 1 then
		error("some of the data could not be decoded", error_level)
	end
	return result
end
local function ValueToBytes(value, external_values, omit_unsupported_values, error_level)
	error_level = CheckErrorLevel(error_level)
	if external_values ~= nil and type(external_values) ~= "table" then
		error("argument #2 to ValueToBytes must be a table or nil", error_level)
	end
	local state = CreateEncodeState()
	state.num_values_omitted = omit_unsupported_values and 0
	if external_values then
		local entries, num_entries = state.entries, #external_values
		for i = 1, num_entries do
			local external_value = external_values[i]
			entries[external_value] = i - 1
		end
		state.num_entries = num_entries
	end
	if value ~= nil then
		EncodeValue(state, value, error_level)
	end
	if omit_unsupported_values then
		return state.buffer, state.num_values_omitted
	else
		return state.buffer
	end
end

local invalid_byte_detected
local NUM_TO_R85 = {}
local R85_TO_NUM = setmetatable({}, {__index = function(self, byte)
	if byte then
		invalid_byte_detected = byte
	end
	return 0
end})
do  local R85_SYMBOLS = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#"
	for i = 0, 84 do
		local symbol = R85_SYMBOLS:sub(i + 1, i + 1)
		R85_TO_NUM[strbyte(symbol)], NUM_TO_R85[i] = i, symbol
	end
end
local R85_COMPRESSION_SYMBOLS = {",", ";", "_", "`", "|", "~"}
local NUM_COMPRESSION_SYMBOLS = #R85_COMPRESSION_SYMBOLS

local function R85ToBlock(r85_str, index, error_level)
	local r0, r1, r2, r3, r4 = strbyte(r85_str, index, index + 4)
	invalid_byte_detected = nil
	local block = (((R85_TO_NUM[r4] * 85 + R85_TO_NUM[r3]) * 85 + R85_TO_NUM[r2]) * 85 + R85_TO_NUM[r1]) * 85 + R85_TO_NUM[r0]
	if invalid_byte_detected then
		local character = (invalid_byte_detected < 32 or invalid_byte_detected > 126) and "\\" .. invalid_byte_detected or strchar(invalid_byte_detected)
		error("invalid byte " .. invalid_byte_detected .. " ('" .. character .. "') in data", error_level + 1)
	end
	return block, index + 5
end
local function R85ToBytes(r85_str, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(r85_str) ~= "string" then
		error("data must be a string", error_level)
	end
	local index = 1
	invalid_byte_detected = nil
	local header = 84 - R85_TO_NUM[strbyte(r85_str, index)]
	if invalid_byte_detected then
		error("invalid data header", error_level)
	end
	index = index + 1
	local bytes_to_discard = header % 4
	local compression_map = {}
	local num_compressions = (header - bytes_to_discard) * 0.25
	if num_compressions > 6 or num_compressions % 1 ~= 0 then
		error("invalid data header", error_level)
	end
	for i = 1, num_compressions do
		compression_map[strbyte(R85_COMPRESSION_SYMBOLS[i])], index = R85ToBlock(r85_str, index, error_level)
	end
	local bytes, bytes_i = {}, 1
	local data_length = #r85_str
	while index <= data_length do
		local r0, block = strbyte(r85_str, index)
		block = compression_map[r0]
		if block then
			index = index + 1
		else
			block, index = R85ToBlock(r85_str, index, error_level)
		end
		for i = 0, 3 do
			local byte = block % 0x100
			block = (block - byte) * 0.00390625
			bytes[bytes_i + i] = byte
		end
		bytes_i = bytes_i + 4
	end
	for i = 1, bytes_to_discard do
		bytes[bytes_i - i] = nil
	end
	return bytes
end

local function BlockToR85(block, buffer, buffer_i)
	for i = 0, 4 do
		local r85_digit = block % 85
		block = (block - r85_digit) / 85
		buffer[buffer_i + i] = NUM_TO_R85[r85_digit]
	end
	return buffer_i + 5
end
local function BytesToR85(bytes, error_level)
	error_level = CheckErrorLevel(error_level)
	local bytes_type = type(bytes)
	if bytes_type == "string" then
		bytes = StringToBytes(bytes)
	elseif bytes_type ~= "table" then
		error("argument #1 must be a table or string", error_level)
	end
	local bytes_n = #bytes
	local bytes_to_discard = -bytes_n % 4
	local buffer = {false}
	local blocks, block_occurrences, most_common_blocks, common_threshold = {}, {}, {}, 1
	local block_i = 1
	for i = 1, bytes_n, 4 do
		local block = (((bytes[i + 3] or 0) * 0x100 + (bytes[i + 2] or 0)) * 0x100 + (bytes[i + 1] or 0)) * 0x100 + bytes[i]
		blocks[block_i], block_i = block, block_i + 1
		local occurrences = (block_occurrences[block] or 0) + 1
		block_occurrences[block] = occurrences
		if occurrences > common_threshold then
			local is_new_block = not most_common_blocks[block]
			most_common_blocks[block] = occurrences
			if is_new_block then
				local num_blocks, least_occurrences, second_least_occurrences, least_common_block = 0, MATH_INF
				for block, occurrences in next, most_common_blocks do
					num_blocks = num_blocks + 1
					if occurrences < least_occurrences then
						least_common_block, least_occurrences, second_least_occurrences = block, occurrences, least_occurrences
					end
				end
				if num_blocks > NUM_COMPRESSION_SYMBOLS then
					common_threshold, most_common_blocks[least_common_block] = second_least_occurrences
				end
			end
		end
	end
	local compression_map, num_compressed_blocks = {}, 0
	local buffer_i = 2
	for common_block in next, most_common_blocks do
		num_compressed_blocks = num_compressed_blocks + 1
		compression_map[common_block] = R85_COMPRESSION_SYMBOLS[num_compressed_blocks]
		buffer_i = BlockToR85(common_block, buffer, buffer_i)
	end
	buffer[1] = NUM_TO_R85[84 - bytes_to_discard - 4 * num_compressed_blocks]
	for i = 1, #blocks do
		local block = blocks[i]
		local compressed_symbol = compression_map[block]
		if compressed_symbol then
			buffer[buffer_i], buffer_i = compressed_symbol, buffer_i + 1
		else
			buffer_i = BlockToR85(blocks[i], buffer, buffer_i)
		end
	end
	local ZERO_SYMBOL = NUM_TO_R85[0]
	for i = 1, 4 do
		local symbol = buffer[buffer_i - i]
		if compression_map[symbol] or symbol ~= ZERO_SYMBOL then
			break
		end
		buffer[buffer_i - i] = nil
	end
	return tblconcat(buffer)
end

local function DecryptBytes(cipher, key, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(cipher) ~= "table" then
		error("argument #1 to DecryptBytes must be a table", error_level)
	end
	local key_type = type(key)
	if key_type == "string" then
		key = StringToBytes(key)
	elseif key_type ~= "table" then
		error("decryption key must be a string or table", error_level)
	end
	local key_length = #key
	if key_length < 1 then
		error("decryption key must contain at least one byte", error_level)
	end
	local cipher_length = #cipher
	local random_bytes = {}
	local random_seed = (cipher_length - key_length + 1) * 57163
	for i = 1, key_length do
		random_seed = (random_seed + key[i] * i) % 4194304 * 1103515245 + 12345
		random_seed = (random_seed + (i + 101) * (random_seed - random_seed % 0x10000) * 1.52587890625e-005)
	end
	for i = 1, (cipher_length - key_length + 1) * key_length do
		random_seed = (random_seed % 4194304 * 1103515245 + 12345)
		random_bytes[i] = (random_seed - random_seed % 0x10000) * 1.52587890625e-005 % 0x100
	end
	local random_i = #random_bytes
	local last_key_byte = key[key_length]
	local buffer = {}
	for i = cipher_length, key_length, -1 do
		local buffer_byte = cipher[i] - last_key_byte
		if buffer_byte < 0 then
			buffer_byte = buffer_byte + 256
		end
		buffer_byte = buffer_byte - random_bytes[random_i]
		random_i = random_i - 1
		if buffer_byte < 0 then
			buffer_byte = buffer_byte + 256
		end
		for j = key_length - 1, 1, -1 do
			i = i - 1
			local cipher_byte = cipher[i] - key[j] - buffer_byte - random_bytes[random_i]
			random_i = random_i - 1
			cipher[i] = cipher_byte % 256
		end
		buffer[i] = buffer_byte
	end
	local buffer_n = #buffer
	for i = 1, buffer_n do
		cipher[i] = buffer[i]
	end
	for i = buffer_n + 1, cipher_length do
		cipher[i] = nil
	end
	return cipher
end

local function EncryptBytes(data, key, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(data) ~= "table" then
		error("argument #1 to EncryptBytes must be a table", error_level)
	end
	local key_type = type(key)
	if key_type == "string" then
		key = StringToBytes(key)
	elseif key_type ~= "table" then
		error("encryption key must be a string or table", error_level)
	end
	local key_length = #key
	if key_length < 1 then
		error("encryption key must contain at least one byte", error_level)
	end
	local data_length = #data
	local buffer = {}
	local random_seed = data_length * 57163
	for i = 1, key_length do
		random_seed = (random_seed + key[i] * i) % 4194304 * 1103515245 + 12345
		random_seed = (random_seed + (i + 101) * (random_seed - random_seed % 0x10000) * 1.52587890625e-005)
	end
	for i = 1, data_length do
		local data_byte = data[i]
		for j = 1, key_length do
			local key_byte = key[j]
			local k = i + j - 1
			local result_byte = data_byte + (buffer[k] or 0)
			random_seed = (random_seed % 4194304 * 1103515245 + 12345)
			buffer[k] = (result_byte + key_byte + (random_seed - random_seed % 0x10000) * 1.52587890625e-005) % 0x100
		end
	end
	for i = 1, #buffer do
		data[i] = buffer[i]
	end
	return data
end

local function DecryptString(data, key, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(data) ~= "string" then
		error("argument #1 to DecryptString must be a string", error_level)
	end
	return BytesToString(DecryptBytes(R85ToBytes(data, error_level), key, error_level))
end

local function EncryptString(data, key, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(data) ~= "string" then
		error("argument #1 to EncryptString must be a string", error_level)
	end
	return BytesToR85(EncryptBytes(StringToBytes(data), key, error_level), error_level)
end

local function CreateLibrary(name, contents)
	local library = newproxy and newproxy(true) or setmetatable({}, {})
	local metatable = getmetatable(library)
	metatable.__metatable = "The metatable is locked"
	metatable.__index = contents
	function metatable.__newindex()
		error("attempt to modify a library", 2)
	end
	function metatable.__tostring()
		return name
	end
	return library
end

LuaData.BytesToString = BytesToString
LuaData.StringToBytes = StringToBytes
LuaData.BytesToValue = BytesToValue
LuaData.ValueToBytes = ValueToBytes
LuaData.R85ToBytes = R85ToBytes
LuaData.BytesToR85 = BytesToR85
LuaData.DecryptBytes = DecryptBytes
LuaData.EncryptBytes = EncryptBytes
LuaData.DecryptString = DecryptString
LuaData.EncryptString = EncryptString

function LuaData.Decode(data, external_values, crypt_key, error_level)
	error_level = CheckErrorLevel(error_level)
	data = R85ToBytes(data, error_level)
	if crypt_key then
		DecryptBytes(data, crypt_key, error_level)
	end
	return BytesToValue(data, external_values, error_level)
end
function LuaData.Encode(value, external_values, crypt_key, omit_unsupported_values, error_level)
	error_level = CheckErrorLevel(error_level)
	local data, num_values_omitted = ValueToBytes(value, external_values, omit_unsupported_values, error_level)
	if crypt_key then
		EncryptBytes(data, crypt_key, error_level)
	end
	data = BytesToR85(data, error_level)
	if omit_unsupported_values then
		return data, num_values_omitted
	else
		return data
	end
end

--script = nil
return CreateLibrary("LuaData", LuaData)
