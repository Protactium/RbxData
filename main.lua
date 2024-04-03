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
RbxData is a wrapper for the LuaData module that adds support for userdata
values defined by ROBLOX, and tables with metatables.

-- How to use:
RbxData = require(path.to.RbxData) -- Requires the module

-- API:
variant  RbxData.Decode(string data, table external_values = nil, variant crypt_key = nil)
string   RbxData.Encode(variant value, array external_values = nil, variant crypt_key = nil, variant ignore = nil, boolean no_hashing = false)
variant  RbxData.BytesToValue(array data, table external_values = nil)
array    RbxData.ValueToBytes(variant value, array external_values = nil, variant ignore = nil, boolean no_hashing = false)
variant  RbxData.ConvertToRbxData(table wrapped_value)
table    RbxData.ConvertToLuaData(variant value, array external_values = nil, variant ignore = nil, boolean no_hashing = false)

-- Inherited from LuaData:
array    RbxData.R85ToBytes(string r85_str)
string   RbxData.BytesToR85(array bytes)
string   RbxData.BytesToString(array bytes, number start_index = 1, number end_index = #bytes)
array    RbxData.StringToBytes(string str, table destination = nil)
array    RbxData.DecryptBytes(array bytes, variant crypt_key)
array    RbxData.EncryptBytes(array bytes, variant crypt_key)
string   RbxData.DecryptString(string cipher, variant crypt_key)
string   RbxData.EncryptString(string plaintext, variant crypt_key)

-- Notes:
1. The output of RbxData.Encode is string-safe, meaning it can be put between
  double quotes (") without being edited in any way.
2. If an instance is encoded, then all of its descendants will automatically be
  encoded as well. However, properties referencing other instances, such the
  'Parent' property, will only be encoded if the other instance is:
  (a) The key or value of a table that is being encoded (recursively).
  (b) A descendant of another instance that is being encoded.
  (c) A descendant of JointsService.
  (d) An external value.
3. Unreadable/unsettable instance properties, such as custom meshes, solid
  modelling and script source cannot be encoded or decoded (although the latter
  can be, but only if the script is executed from the command prompt in ROBLOX
  Studio).
4. The 'external_values' parameter can have a member called 'n' when decoding,
  indicating the number of values it contains. This can be used to substitue
  external values with nil values when decoding.
5. The 'ignore' parameter of RbxData.Encode, RbxData.ValueToBytes and
  RbxData.ConvertToLuaData can be either an array of instances, a table with
  instances as keys (which is allowed to use a metatable with the __index
  metamethod), or a function, returning true if the instance should not be
  encoded.
6. The 'no_hashing' parameter of RbxData.Encode, RbxData.ValueToBytes and
  RbxData.ConvertToLuaData can be used to disable hashing of readonly userdatas
  (which is turned on by default). Turning off hashing will make the encoding
  process faster, but it will result in a larger output and slightly slower
  decoding process.
7. Terrain currently cannot be encoded.
--]]

local RbxData = {}

local LuaData = require(script.Parent.LuaData)

local LuaData_BytesToString, LuaData_BytesToValue, LuaData_ValueToBytes, LuaData_R85ToBytes, LuaData_BytesToR85, LuaData_DecryptBytes, LuaData_EncryptBytes
    = LuaData.BytesToString, LuaData.BytesToValue, LuaData.ValueToBytes, LuaData.R85ToBytes, LuaData.BytesToR85, LuaData.DecryptBytes, LuaData.EncryptBytes

local    dbgtraceback, error, getmetatable, next, rawset, setmetatable,    tblinsert,    tblremove, tostring, type, unpack, xpcall
    = debug.traceback, error, getmetatable, next, rawset, setmetatable, table.insert, table.remove, tostring, type, unpack, xpcall
local Enum, game, Instance_new, newproxy, typeof, warn = Enum, game, Instance.new, newproxy, typeof, warn
local JointsService = game:GetService("JointsService")

local UnwrapValue, WrapValue

-- Do CFrame first so that Position, Rotation, etc. can be ignored
-- BrickColor properties are not included if there is a Color3 alternative
local PROPERTY_NAMES = {
	"CFrame", "Acceleration", "Active", "ActuatorType", "Adornee",
	"AllowInsertFreeModels", "AllowTeamChangeOnTouch", "AllowThirdPartySales",
	"AlwaysOnTop", "Ambient", "AmbientReverb", "AnchorPoint", "Anchored",
	"Angle", "AngularActuatorType", "AngularLimitsEnabled",
	"AngularRestitution", "AngularSpeed", "AngularVelocity", "Animated",
	"AnimationId", "ApplyAtCenterOfMass", "Archivable", "AspectRatio",
	"AspectType", "Attachment0", "Attachment1", "AttachmentForward",
	"AttachmentPoint", "AttachmentPos", "AttachmentRight", "AttachmentUp",
	"Attack", "AutoAssignable", "AutoButtonColor", "AutoColorCharacters",
	"AutoJumpEnabled", "AutoRotate", "AutoRuns", "AutoSelectGuiEnabled",
	"Axes", "Axis", "BackParamA", "BackParamB", "BackSurface",
	"BackSurfaceInput", "BackgroundColor3",
	"BackgroundTransparency", "BaseAngle", "BaseTextureId", "BehaviorType",
	"BinType", "BlastPressure", "BlastRadius", "BodyPart",
	"BorderColor3", "BorderSizePixel", "BottomImage", "BottomParamA",
	"BottomParamB", "BottomSurface", "BottomSurfaceInput",
	"Brightness", "Browsable", "C0", "C1", "CameraMaxZoomDistance",
	"CameraMinZoomDistance", "CameraMode", "CameraOffset", "CameraSubject",
	"CameraType", "CanBeDropped", "CanCollide", "CanvasPosition", "CanvasSize",
	"CartoonFactor", "CelestialBodiesShown", "CellPadding", "CellSize",
	"CharacterAutoLoads", "Circular", "ClassCategory", "ClearTextOnFocus",
	"ClipsDescendants", "ClockTime", "Coils", "CollisionGroupId", "Color",
	"Color3", "ConstrainedValue", "Contrast", "ConversationDistance",
	"CoreGuiNavigationEnabled", "CurrentAngle",
	"CurrentCamera", "CursorIcon", "CustomPhysicalProperties",
	"CustomizedTeleportUI", "CycleOffset", "D", "Damping", "DecayTime",
	"Delay", "Density", "Deprecated", "Depth", "Description", "DesiredAngle",
	"DestroyJointRadiusPercent", "DevCameraOcclusionMode",
	"DevComputerCameraMovementMode", "DevComputerMovementMode",
	"DevTouchCameraMovementMode", "DevTouchMovementMode",
	"DevelopmentLanguage", "Diffusion", "Disabled", "DisplayDistanceType",
	"DisplayOrder", "DistanceFactor", "DistributedGameTime", "DominantAxis",
	"DopplerScale", "Drag", "Draggable", "DryLevel", "Duration", "Duty",
	"EasingDirection", "EasingStyle", "EditingDisabled",
	"EmissionDirection", "EmitterSize", "EmptyCutoff", "EnableMouseLockOption",
	"Enabled", "ExplorerImageIndex", "ExplorerOrder", "ExplosionType",
	"ExtentsOffset", "ExtentsOffsetWorldSpace", "F0", "F1", "F2", "F3", "Face",
	"FaceCamera", "FaceId", "Faces", "Feedback", "FieldOfView",
	"FillDirection", "FillDirectionMaxCells", "FillEmptySpaceColumns",
	"FillEmptySpaceRows", "Focus", "FogColor", "FogEnd", "FogStart", "Font",
	"FontSize", "Force", "FreeLength", "Frequency",
	"From", "FrontParamA", "FrontParamB", "FrontSurface", "FrontSurfaceInput",
	"GainMakeup", "GamepadInputEnabled", "GeographicLatitude", "GlobalShadows",
	"GoodbyeChoiceActive", "GoodbyeDialog", "Graphic", "Gravity", "Grip",
	"GripForward", "GripPos", "GripRight", "GripUp", "GuiInputUserCFrame",
	"GuiNavigationEnabled", "HeadColor3", "HeadLocked",
	"HeadScale", "HeadsUpDisplay", "Health", "HealthDisplayDistance",
	"HealthDisplayType", "Heat", "Height", "HighGain", "HipHeight", "Hole",
	"HorizontalAlignment", "HorizontalScrollBarInset", "Humanoid", "Image",
	"ImageColor3", "ImageRectOffset", "ImageRectSize", "ImageTransparency",
	"InOut", "InUse", "InclinationAngle", "InitialPrompt", "Insertable",
	"Intensity", "InverseSquareLaw", "Is30FpsThrottleEnabled", "IsBackend",
	"IsPhysicsEnvironmentalThrottled", "IsSleepAllowed", "Jump", "JumpPower",
	"LayoutOrder", "LeftArmColor3", "LeftLeg", "LeftLegColor3",
	"LeftParamA", "LeftParamB", "LeftRight", "LeftSurface",
	"LeftSurfaceInput", "Length", "Level", "Lifetime", "LightEmission",
	"LightInfluence", "LimitsEnabled", "LineThickness", "LinkedSource",
	"LoadCharacterAppearance", "LocalTransparencyModifier", "Localize",
	"Location", "Locked", "LockedToPart", "Loop", "Looped", "LowGain",
	"LowerAngle", "LowerLimit", "Magnitude", "MajorAxis",
	"ManualActivationOnly", "MaskWeight", "Material", "MaxActivationDistance",
	"MaxAngularVelocity", "MaxDistance", "MaxForce", "MaxHealth", "MaxLength",
	"MaxSize", "MaxSlopeAngle", "MaxSpeed", "MaxTextSize", "MaxThrust",
	"MaxTorque", "MaxValue", "MaxVelocity", "MeshId", "MeshType", "MidGain",
	"MidImage", "MinDistance", "MinLength", "MinSize", "MinTextSize",
	"MinValue", "Mix", "Modal", "ModalEnabled", "MoonAngularSize",
	"MoonTextureId", "MotorMaxAcceleration", "MotorMaxAngularAcceleration",
	"MotorMaxForce", "MotorMaxTorque", "MouseBehavior",
	"MouseDeltaSensitivity", "MouseIconEnabled", "MultiLine", "Name",
	"NameDisplayDistance", "NameOcclusion", "Neutral", "NextSelectionDown",
	"NextSelectionLeft", "NextSelectionRight", "NextSelectionUp",
	"NumberOfPlayers", "Octave", "Offset", "Opacity", "Orientation",
	"OutdoorAmbient", "Outlines", "OverlayTextureId", "P", "Padding",
	"PaddingBottom", "PaddingLeft", "PaddingRight", "PaddingTop", "PantsTemplate",
	"Parent", "Part", "Part0", "Part1", "Pitch", "PlaceholderColor3",
	"PlaceholderText", "PlatformStand", "PlayOnRemove", "PlaybackSpeed",
	"PlayerToHideFrom", "Playing", "Point", "Position", "PreferredParent",
	"PrimaryAxisOnly", "PrimaryPart", "Priority", "Purpose", "Radius", "Range",
	"Rate", "Ratio", "ReactionForceEnabled", "ReactionTorqueEnabled",
	"Reflectance", "RelativeTo", "Release", "RequiresHandle", "ResetOnSpawn",
	"ResetPlayerGuiOnSpawn", "RespectFilteringEnabled", "ResponseDialog",
	"Responsiveness", "Restitution", "RigType",
	"RightArmColor3", "RightLeg", "RightLegColor3",
	"RightParamA", "RightParamB", "RightSurface", "RightSurfaceInput",
	"RigidityEnabled", "RiseVelocity", "RollOffMode", "RolloffScale", "Root",
	"RotSpeed", "RotVelocity", "Rotation", "Saturation", "Scale", "ScaleType",
	"Score", "ScreenOrientation", "ScrollBarThickness",
	"ScrollWheelInputEnabled", "ScrollingEnabled", "SecondaryAxis",
	"SecondaryColor", "Selectable", "Selected", "SelectedObject",
	"SelectionImageObject", "ServoMaxForce", "ServoMaxTorque", "ShadowColor",
	"Shadows", "Shape", "Shiny", "ShirtTemplate", "ShowDevelopmentGui",
	"ShowNativeInput", "SideChain", "SimulateSecondsLag", "Sit", "Size",
	"SizeConstraint", "SizeFromContents", "SizeOffset", "SizeRelativeOffset",
	"SkinColor", "SkyboxBk", "SkyboxDn", "SkyboxFt", "SkyboxLf", "SkyboxRt",
	"SkyboxUp", "SliceCenter", "SortOrder", "SoundGroup", "SoundId", "Source",
	"SparkleColor", "Specular", "Speed", "Spread", "SpreadAngle", "StarCount",
	"StartCorner", "Steer", "SteerFloat", "StickyWheels", "Stiffness",
	"StreamingEnabled", "StudsBetweenTextures", "StudsOffset",
	"StudsOffsetWorldSpace", "StudsPerTileU", "StudsPerTileV", "Style",
	"SunAngularSize", "SunTextureId", "SurfaceColor3",
	"SurfaceTransparency", "Target", "TargetAngle", "TargetOffset",
	"TargetPoint", "TargetPosition", "TargetRadius", "TargetSurface",
	"TeamColor", "Text","TextColor3", "TextScaled", "TextSize",
	"TextStrokeColor3", "TextStrokeTransparency", "TextTransparency",
	"TextWrap", "TextWrapped", "TextXAlignment", "TextYAlignment", "Texture",
	"TextureID", "TextureId", "TextureLength", "TextureMode", "TextureSize",
	"Thickness", "Threshold", "Throttle", "ThrottleFloat", "ThrustD",
	"ThrustP", "Ticket", "TileSize", "Time", "TimeOfDay", "TimePosition",
	"Timeout", "TintColor", "To", "Tone", "ToolPunchThroughDistance",
	"ToolTip", "TopBottom", "TopImage", "TopParamA", "TopParamB", "TopSurface",
	"TopSurfaceInput", "Torque", "Torso", "TorsoColor3",
	"TouchInputEnabled", "Transform", "Transparency", "TriggerDistance",
	"TriggerOffset", "TurnD", "TurnP", "TurnSpeed", "TweenTime",
	"TwistLimitsEnabled", "TwistLowerAngle", "TwistUpperAngle", "UIMaximum",
	"UIMinimum", "UINumTicks", "UpperAngle", "UpperLimit", "UsePartColor",
	"UserDialog", "Value", "Velocity", "VelocityInheritance", "VelocitySpread",
	"VertexColor", "VerticalAlignment", "VerticalScrollBarInset",
	"VerticalScrollBarPosition", "Visible", "Volume", "WalkSpeed",
	"WalkToPart", "WalkToPoint", "Weight", "WetLevel", "WireRadius", "ZIndex",
	"ZOffset", "summary"
}

local function CheckErrorLevel(error_level)
	if error_level == nil then
		return 2
	elseif type(error_level) ~= "number" then
		error("error level must be a number or nil", 3)
	end
	return error_level + 1
end
local function DummyFunction()
end

local function CanSetProperty(object, property)
	return xpcall(function() object[property] = object[property] end, DummyFunction)
end

local CFRAME_ALTERNATIVES = {
	Position = true, Orientation = true, Rotation = true, Axis = true, SecondaryAxis = true
}
local function GetSettableProperties(object)
	local properties, current_values = {}, {}
	local has_cframe = false
	for i = 1, #PROPERTY_NAMES do
		local property = PROPERTY_NAMES[i]
		if not (has_cframe and CFRAME_ALTERNATIVES[property]) and CanSetProperty(object, property) then
			if property == "CFrame" then
				has_cframe = true
			end
			properties[#properties + 1] = property
			current_values[property] = object[property]
		end
	end
	return properties, current_values
end

local INSTANCE_CLASS_INFO = setmetatable({}, {__index = function(self, classname)
	local success, instance = xpcall(function() return Instance_new(classname) end, DummyFunction)
	local info
	if success then
		local properties, defaults = GetSettableProperties(instance)
		info = {service = false, properties = properties, defaults = defaults}
	else
		success, instance = xpcall(function() return game:GetService(classname) end, DummyFunction)
		if success then
			info = {service = true, properties = GetSettableProperties(instance)}
		else
			info = false
		end
	end
	rawset(self, classname, info)
	return info
end})

local function SetProperties(state, object, properties)
	for property, value in next, properties do
		if not xpcall(function() object[property] = UnwrapValue(state, value) end, DummyFunction) then
			warn("property '" .. tostring(property) .. "' could not be set to '" .. tostring(UnwrapValue(state, value)) .. "' for instance of type '" .. object.ClassName .. "'")
		end
	end
	return object
end

local DECODERS = {}

local _ENV = _ENV or getfenv()
-- Load default constructors where applicable
for _, type_name in ipairs {
	"BrickColor", "CFrame", "Color3", "ColorSequenceKeypoint", "NumberRange",
	"NumberSequenceKeypoint", "PhysicalProperties", "TweenInfo", "UDim", "UDim2",
	"Vector2", "Vector2int16", "Vector3", "Vector3int16"
} do
	local constructor = _ENV[type_name].new
	DECODERS[type_name] = function(args)
		return constructor(unpack(args))
	end
end

local AXIS_ENUM_ITEMS = {Enum.Axis.X, Enum.Axis.Y, Enum.Axis.Z}
local NORMALID_ENUM_ITEMS = {Enum.NormalId.Right, Enum.NormalId.Left, Enum.NormalId.Top, Enum.NormalId.Bottom, Enum.NormalId.Back, Enum.NormalId.Front}

local function MakeBitDecoder(constructor, items)
	return function(data)
		local args = {}
		local bits = data[1]
		for i = 1, #items do
			local bit = bits % 2
			if bit == 1 then
				args[#args + 1] = items[i]
			end
			bits = (bits - bit) * 0.5
		end
		return constructor(unpack(args))
	end
end
local function MakeSequenceDecoder(constructor, sub_constructor)
	return function(keypoints)
		for i = 1, #keypoints do
			keypoints[i] = sub_constructor(unpack(keypoints[i]))
		end
		return constructor(keypoints)
	end
end
local function MakeTwoArgumentDecoder(constructor, sub_constructor)
	return function(data)
		return constructor(sub_constructor(unpack(data[1])), sub_constructor(unpack(data[2])))
	end
end

function DECODERS.__metatable(data)
	local metatable = data[2]
	if type(metatable) ~= "table" then
		metatable = {__metatable = metatable}
	end
	return setmetatable(data[1], metatable)
end
function DECODERS.__service(data, state)
	local service = game:GetService(data[1])
	state.unwrapped_map[data] = service
	return SetProperties(state, service, data[2])
end

function DECODERS.userdata(data)
	local metatable = data[1]
	local object = newproxy(metatable ~= nil)
	if metatable then
		local object_metatable = getmetatable(object)
		for key, value in next, metatable do
			object_metatable[key] = value
		end
	end
	return object
end
function DECODERS.Instance(data, state)
	local instance = Instance_new(data[1])
	state.unwrapped_map[data] = instance
	SetProperties(state, instance, data[2])
	local parent = data[3]
	if parent then
		instance.Parent = UnwrapValue(state, data[3])
	end
	return instance
end

function DECODERS.EnumItem(data)
	return Enum[data[1]][data[2]]
end
DECODERS.Axes = MakeBitDecoder(Axes.new, AXIS_ENUM_ITEMS)
DECODERS.ColorSequence = MakeSequenceDecoder(ColorSequence.new, DECODERS.ColorSequenceKeypoint)
DECODERS.Faces = MakeBitDecoder(Faces.new, NORMALID_ENUM_ITEMS)
DECODERS.NumberSequence = MakeSequenceDecoder(NumberSequence.new, DECODERS.NumberSequenceKeypoint)
DECODERS.Ray = MakeTwoArgumentDecoder(Ray.new, Vector3.new)
DECODERS.Rect = MakeTwoArgumentDecoder(Rect.new, Vector2.new)
DECODERS.Region3 = MakeTwoArgumentDecoder(Region3.new, Vector3.new)
DECODERS.Region3int16 = MakeTwoArgumentDecoder(Region3int16.new, Vector3int16.new)
DECODERS.UDim2 = MakeTwoArgumentDecoder(UDim2.new, UDim.new)

local ENCODERS = {}
local BOOLEAN_TO_NUM = {[false] = 0, [true] = 1}

function ENCODERS.userdata(value, state)
	local data = {}
	state.wrappers[value] = data
	local metatable = getmetatable(value)
	if type(metatable) == "table" then
		data[1] = WrapValue(state, metatable)
	end
	return data
end
function ENCODERS.Instance(value, state)
	local success, classname = xpcall(function() return value.ClassName end, DummyFunction)
	if not success then return end
	local class_info = INSTANCE_CLASS_INFO[classname]
	if not class_info then return end
	local settable_properties, defaults = class_info.properties, class_info.defaults
	local properties = {}
	local data = {classname, properties}
	state.wrappers[value] = data
	for i = 1, #settable_properties do
		local property_name = settable_properties[i]
		local success, property_value = xpcall(function() return value[property_name] end, DummyFunction)
		if success and (not defaults or property_value ~= defaults[property_name]) then
			properties[property_name] = WrapValue(state, property_value)
		end
	end
	local is_service = class_info.service
	data[3], properties.Parent = (not is_service) and properties.Parent or nil
	return data, is_service and "__service"
end

local function EncodeColorSequenceKeypoint(value)
	return {value.Time, value.Value}
end
local function EncodeNumberSequenceKeypoint(value)
	return {value.Time, value.Value, value.Envelope}
end
local function EncodeUDim(value)
	return {value.Scale, value.Offset}
end
local function EncodeVector2(value)
	return {value.X, value.Y}
end
local function EncodeVector3(value)
	return {value.X, value.Y, value.Z}
end

function ENCODERS.EnumItem(value)
	return {tostring(value.EnumType), value.Name}
end
function ENCODERS.Axes(value)
	return {BOOLEAN_TO_NUM[value.X] + 2 * (BOOLEAN_TO_NUM[value.Y] + 2 * BOOLEAN_TO_NUM[value.Z])}
end
function ENCODERS.BrickColor(value)
	return {value.Number}
end
function ENCODERS.CFrame(value)
	return {value:components()}
end
function ENCODERS.Color3(value)
	return {value.r, value.g, value.b}
end
function ENCODERS.ColorSequence(value)
	local keypoints = value.Keypoints
	local data = {}
	for i = 1, #keypoints do
		data[i] = EncodeColorSequenceKeypoint(keypoints[i])
	end
	return data
end
ENCODERS.ColorSequenceKeypoint = EncodeColorSequenceKeypoint
function ENCODERS.Faces(value)
	return {
		BOOLEAN_TO_NUM[value.Right] + 2 * (BOOLEAN_TO_NUM[value.Left] + 2 *
		(BOOLEAN_TO_NUM[value.Top] + 2 * (BOOLEAN_TO_NUM[value.Bottom] + 2 *
		(BOOLEAN_TO_NUM[value.Back] + 2 * BOOLEAN_TO_NUM[value.Front]))))
	}
end
function ENCODERS.NumberRange(value)
	return {value.Min, value.Max}
end
function ENCODERS.NumberSequence(value)
	local keypoints = value.Keypoints
	local data = {}
	for i = 1, #keypoints do
		data[i] = EncodeNumberSequenceKeypoint(keypoints[i])
	end
	return data
end
ENCODERS.NumberSequenceKeypoint = EncodeNumberSequenceKeypoint
function ENCODERS.PhysicalProperties(value)
	return {value.Density, value.Friction, value.Elasticity, value.FrictionWeight, value.ElasticityWeight}
end
function ENCODERS.Ray(value)
	local origin, direction = value.Origin, value.Direction
	return {EncodeVector3(value.Origin), EncodeVector3(value.Direction)}
end
function ENCODERS.Rect(value)
	return {EncodeVector2(value.Min), EncodeVector2(value.Max)}
end
function ENCODERS.Region3(value)
	local center, half_size = value.CFrame.p, 0.5 * value.Size
	local min, max = center - half_size, center + half_size
	return {EncodeVector3(min), EncodeVector3(max)}
end
function ENCODERS.Region3int(value)
	return {EncodeVector3(value.Min), EncodeVector3(value.Max)}
end
function ENCODERS.TweenInfo(value)
	return {value.Time, value.EasingStyle.Value, value.EasingDirection.Value, value.RepeatCount, value.Reverses, value.DelayTime}
end
ENCODERS.UDim = EncodeUDim
function ENCODERS.UDim2(value)
	return {EncodeUDim(value.X), EncodeUDim(value.Y)}
end
ENCODERS.Vector2 = EncodeVector2
ENCODERS.Vector2int16 = ENCODERS.Vector2
ENCODERS.Vector3 = EncodeVector3
ENCODERS.Vector3int16 = EncodeVector3

local NATIVE_TYPES = {boolean = true, number = true, string = true, table = true}
local NIL_REF = {}

function UnwrapValue(state, wrapped_value)
	local unwrapped_map = state.unwrapped_map
	local value = unwrapped_map[wrapped_value]
	if value then
		return value
	end
	local constructors = state.constructors
	local type_name = constructors[wrapped_value]
	if type_name then
		local decoder = DECODERS[type_name]
		if not decoder then
			error("attempt to decode value of unknown type '" .. tostring(type_name) .. "'")
		end
		value = decoder(wrapped_value, state)
	else
		value = wrapped_value
	end
	unwrapped_map[wrapped_value] = value
	if type(value) == "table" then
		for key, child in next, value do
			value[UnwrapValue(state, key)] = UnwrapValue(state, child)
		end
	end
	return value
end

function WrapValue(state, value)
	local constructors, wrappers = state.constructors, state.wrappers
	local wrapper = wrappers[value]
	if wrapper then
		return wrapper
	end
	local value_type = type(value)
	if NATIVE_TYPES[value_type] then
	 	if value_type == "table" then
			local wrapped_table, mt_wrapper = {}
			local metatable = getmetatable(value)
			if type(metatable) == "table" then
				mt_wrapper = {wrapped_table}
				wrappers[value] = mt_wrapper
				constructors[mt_wrapper] = "__metatable"
				mt_wrapper[2] = WrapValue(state, metatable)
			else
				wrappers[value] = wrapped_table
			end
			for key, value in next, value do
				local wrapped_key, wrapped_value = WrapValue(state, key), WrapValue(state, value)
				if wrapped_key then
					wrapped_table[wrapped_key] = wrapped_value
				end
			end
			return mt_wrapper or wrapped_table
		else
			return value
		end
	elseif value_type == "userdata" then
		value_type = typeof(value)
		local is_instance = value_type == "Instance"
		if not is_instance or state.whitelist[value] then
			local encoder = ENCODERS[value_type]
			if encoder then
				local data, decode_type = encoder(value, state)
				if data then
					decode_type = decode_type or value_type
					local hashes = state.hashes
					if hashes and not is_instance and value_type ~= "userdata" then
						-- all ROBLOX userdata values except Instances are read-only, so they can be hashed so that references can be used for compression
						local hash = LuaData_BytesToString(LuaData_ValueToBytes({decode_type, data}))
						local existing_data = hashes[hash]
						if existing_data then
							return existing_data
						else
							hashes[hash] = data
						end
					end
					constructors[data], wrappers[value] = decode_type, data
					if is_instance then
						local success, children = xpcall(function() return value:GetChildren() end, DummyFunction)
						if success then
							for i = 1, #children do
								WrapValue(state, children[i])
							end
						end
					end
					return data
				end
			end
		end
	end
end

local function HandleUnwrapError(error_message)
	local trace = dbgtraceback()
	local end_line = trace:find("\n[^\n]*xpcall") or trace:find("\n[^\n]*ConvertToRbxData") or (#trace + 1)
	return "(error: " .. error_message .. ")\n" .. trace:sub(1, end_line - 1)
end
local function ConvertToRbxData(wrapped_value, error_level)
	error_level = CheckErrorLevel(error_level)
	if type(wrapped_value) ~= "table" then
		error("the data is corrupted and could not be unwrapped", error_level)
	end
	local constructors = wrapped_value[2]
	local state = {constructors = constructors, unwrapped_map = {}}
	local success, result = xpcall(function()
		for data in next, constructors do
			UnwrapValue(state, data)
		end
		local value = wrapped_value[1]
		return value and UnwrapValue(state, value)
	end, HandleUnwrapError)
	if success then
		return result
	else
		error("the data could not be successfully unwrapped " .. result .. "\nTip: make sure to use the same amount of external values when encoding/decoding.", error_level)
	end
end
local function ConvertToLuaData(value, external_values, ignore_list, no_hashing, error_level)
	error_level = CheckErrorLevel(error_level)
	local ignore_list_type, ignore_set, ignore_func = type(ignore_list), {}
	if ignore_list_type == "function" then
		ignore_func, ignore_list = ignore_list
	elseif ignore_list_type == "table" then
		for i = 1, #ignore_list do
			ignore_set[ignore_list[i]] = true
		end
	elseif ignore_list ~= nil then
		error("ignore list must be a table or nil", error_level)
	end
	local wrappers = {}
	if external_values then
		for i = 1, #external_values do
			local value = external_values[i]
			wrappers[value], ignore_set[value] = value, true
		end
	end
	local whitelist = {}
	local stack = {value}
	while #stack > 0 do
		local stack_n, object = #stack
		object, stack[stack_n] = stack[stack_n]
		if not ignore_set[object] and not (ignore_list and ignore_list[object]) and not (ignore_func and ignore_func(object)) then
			ignore_set[object] = true
			local object_type = typeof(object)
			if object_type == "table" then
				for key, value in next, object do
					stack[stack_n], stack[stack_n + 1], stack_n = key, value, stack_n + 2
				end
			elseif object_type == "Instance" then
				whitelist[object] = true
				local success, children = xpcall(function() return object:GetChildren() end, DummyFunction)
				if success then
					for i = 1, #children do
						stack[stack_n + i - 1] = children[i]
					end
				end
			end
		end
	end
	if not whitelist[JointsService] then
		wrappers[JointsService] = JointsService
	end
	local constructors = {}
	local state = {constructors = constructors, wrappers = wrappers, whitelist = whitelist, nil_ref = {}, hashes = not no_hashing and {} or nil}
	local wrapped_value = WrapValue(state, value)
	local joints, joint = JointsService:GetChildren()
	local function CheckJoint()
		return wrappers[joint.Part0] and wrappers[joint.Part1]
	end
	for i = 1, #joints do
		joint = joints[i]
		local success, result = xpcall(CheckJoint, DummyFunction)
		if result then
			whitelist[joint] = true
			WrapValue(state, joint)
		end
	end
	return {wrapped_value, constructors}
end

local function BytesToValue(bytes, external_values, error_level)
	error_level = CheckErrorLevel(error_level)
	if external_values == nil then
		external_values = {}
	elseif type(external_values) ~= "table" then
		error("external values must be a table or nil", error_level)
	end
	local external_values_n = external_values.n
	if external_values_n then
		external_values_n = external_values_n + 1
		external_values[external_values_n], external_values.n = JointsService, external_values_n
	else
		tblinsert(external_values, JointsService)
	end
	local wrapped_value = LuaData_BytesToValue(bytes, external_values, error_level)
	if external_values_n then
		external_values.n, external_values[external_values_n] = external_values_n - 1
	else
		tblremove(external_values)
	end
	return ConvertToRbxData(wrapped_value, error_level)
end
local function ValueToBytes(value, external_values, ignore_list, no_hashing, error_level)
	error_level = CheckErrorLevel(error_level)
	if external_values == nil then
		external_values = {}
	elseif type(external_values) ~= "table" then
		error("external values must be a table or nil", error_level)
	end
	tblinsert(external_values, JointsService)
	local result = LuaData_ValueToBytes(ConvertToLuaData(value, external_values, ignore_list, no_hashing, error_level), external_values, false, error_level)
	tblremove(external_values)
	return result
end

RbxData.ConvertToRbxData = ConvertToRbxData
RbxData.ConvertToLuaData = ConvertToLuaData
RbxData.BytesToValue = BytesToValue
RbxData.ValueToBytes = ValueToBytes

-- inherit from LuaData
RbxData.BytesToString = LuaData_BytesToString
RbxData.StringToBytes = LuaData.StringToBytes
RbxData.R85ToBytes = LuaData_R85ToBytes
RbxData.BytesToR85 = LuaData_BytesToR85
RbxData.DecryptBytes = LuaData_DecryptBytes
RbxData.EncryptBytes = LuaData_EncryptBytes
RbxData.DecryptString = LuaData.DecryptString
RbxData.EncryptString = LuaData.EncryptString

function RbxData.Decode(data, external_values, crypt_key, error_level)
	error_level = CheckErrorLevel(error_level)
	data = LuaData_R85ToBytes(data, error_level)
	if crypt_key then
		LuaData_DecryptBytes(data, crypt_key, error_level)
	end
	return BytesToValue(data, external_values, error_level)
end
function RbxData.Encode(value, external_values, crypt_key, ignore_list, no_hashing, error_level)
	error_level = CheckErrorLevel(error_level)
	local data = ValueToBytes(value, external_values, ignore_list, no_hashing, error_level)
	if crypt_key then
		LuaData_EncryptBytes(data, crypt_key, error_level)
	end
	return LuaData_BytesToR85(data, error_level)
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

script = nil
return CreateLibrary("RbxData", RbxData)
