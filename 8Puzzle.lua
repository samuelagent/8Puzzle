--// Services

local UserInputService = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")

--// Assets

local ScreenGui = script.Parent

local Frame = ScreenGui:WaitForChild("Frame")
local PuzzleFrame = Frame:WaitForChild("PuzzleFrame")

local ImageTextBox = Frame:WaitForChild("TextBox")
local ImageGoButton = Frame:WaitForChild("ImageGo")

local AStarButton = Frame:WaitForChild("AStar")
local DFSButton = Frame:WaitForChild("DFS")
local BFSButton = Frame:WaitForChild("BFS")
local IDSButton = Frame:WaitForChild("IDS")

local SolveButton = Frame:WaitForChild("Solve")
local ScrambleButton = Frame:WaitForChild("Scramble")
local AlgorithmComputeLabel = Frame:WaitForChild("ComputeTime")

local TileFrames = {
	PuzzleFrame:WaitForChild("One"),
	PuzzleFrame:WaitForChild("Two"),
	PuzzleFrame:WaitForChild("Three"),
	PuzzleFrame:WaitForChild("Four"),
	PuzzleFrame:WaitForChild("Five"),
	PuzzleFrame:WaitForChild("Six"),
	PuzzleFrame:WaitForChild("Seven"),
	PuzzleFrame:WaitForChild("Eight"),
	PuzzleFrame:WaitForChild("Nine")
}

local TileImages = {
	TileFrames[1]:WaitForChild("ImageLabel"),
	TileFrames[2]:WaitForChild("ImageLabel"),
	TileFrames[3]:WaitForChild("ImageLabel"),
	TileFrames[4]:WaitForChild("ImageLabel"),
	TileFrames[5]:WaitForChild("ImageLabel"),
	TileFrames[6]:WaitForChild("ImageLabel"),
	TileFrames[7]:WaitForChild("ImageLabel"),
	TileFrames[8]:WaitForChild("ImageLabel"),
	TileFrames[9]:WaitForChild("ImageLabel"),
}

--// Constants

local PICKED_COLOR = Color3.fromRGB(135, 255, 140)
local UNPICKED_COLOR = Color3.fromRGB(255, 150, 150)

--// Variables

local CurrentBatch = os.clock()
local BatchYields = 0
local BatchSize = 0.5

local Solving = false

local CurrentAlgorithm = "AStar"

local CurrentState = {1, 2, 3, 4, 5, 6, 7, 8, 9}
local CurrentGoalState = {1, 2, 3, 4, 5, 6, 7, 8, 9}

local TilePositions = {
	UDim2.new(1/6, 0, 1/6, 0),
	UDim2.new(0.5, 0, 1/6, 0),
	UDim2.new(5/6, 0, 1/6, 0),
	UDim2.new(1/6, 0, 0.5, 0),
	UDim2.new(0.5, 0, 0.5, 0),
	UDim2.new(5/6, 0, 0.5, 0),
	UDim2.new(1/6, 0, 5/6, 0),
	UDim2.new(0.5, 0, 5/6, 0),
	UDim2.new(5/6, 0, 5/6, 0),
}

local ValidKeyCodes = {
	[Enum.KeyCode.W] = "U",
	[Enum.KeyCode.A] = "L",
	[Enum.KeyCode.S] = "D",
	[Enum.KeyCode.D] = "R",
}

local ComputeFunctions = {}

local TileTweenInfo = TweenInfo.new(0.15, Enum.EasingStyle.Sine, Enum.EasingDirection.InOut)

--// Auxiliary

local function clone(oldTable) -- For when we need tables by value not reference
	local newTable = {}
	for i, v in pairs(oldTable) do
		if type(v) == "table" then
			v = clone(v)
		end
		newTable[i] = v
	end
	return newTable
end

local function IsSolvable(Array)
	local Inversions = 0
	for i = 1, 9 do
		for j = i + 1, 9 do
			if Array[j] ~= 9 and Array[i] ~= 9 and Array[j] < Array[i] then
				Inversions += 1
			end
		end
	end
	return Inversions % 2 == 0
end

local function goalState(State) -- Check if given state is the goal state
	for i, v in ipairs(CurrentGoalState) do
		if v ~= State[i] then return false end
	end
	return true
end

local function getDirection(Move) -- Gets the direction from a move
	return Move[1] or error("Invalid format")
end

local function getState(Move) -- Gets the state from a move
	return Move[2] or error("Invalid format")
end

local function sameState(MoveA, MoveB) -- Checks if two moves lead to the same state
	for i, v in ipairs(MoveA[2]) do
		if v ~= MoveB[2][i] then return false end
	end
	return true
end

local function getScrambledPuzzle()
	local Scrambled = {}
	repeat
		Scrambled = {}
		for i, v in ipairs(CurrentGoalState) do
			table.insert(Scrambled, math.random(1, #Scrambled + 1), v)
		end
	until IsSolvable(Scrambled)
	return Scrambled
end

local function path(Moves) -- Gets directions taken in order of first to last from a path
	local Directions = {}
	for Index = #Moves, 1, -1 do
		local direction = getDirection(Moves[Index])
		if direction ~= "nil" then
			table.insert(Directions, direction)	
		end
	end
	return Directions
end

local function removeRedundant(PathA, PathB) -- Returns first path with any identical states as the second path removed
	PathA = clone(PathA)
	for i, v in ipairs(PathA) do
		for o, b in pairs(PathB) do
			if sameState(v, b) then
				table.remove(PathA, i)
				break
			end
		end	
	end
	return PathA
end

local function swapElements(OldTable, a, b)
	local newTable = clone(OldTable) -- Had to add this to make it work
	newTable[a], newTable[b] = newTable[b], newTable[a]
	return newTable
end

local function moves(State) -- Returns all possible moves out of state in path format (Without an initial)
	local EmptyIndex = table.find(State, 9)
	local Openers = {}

	local IndexModulus = EmptyIndex % 3

	if IndexModulus ~= 1 then -- Can move left
		table.insert(Openers, {'L', swapElements(State, EmptyIndex, EmptyIndex - 1)})
	end
	if IndexModulus ~= 0 then -- Can move right
		table.insert(Openers, {'R', swapElements(State, EmptyIndex, EmptyIndex + 1)})
	end
	if EmptyIndex > 3 then -- Can move up
		table.insert(Openers, {'U', swapElements(State, EmptyIndex, EmptyIndex - 3)})
	end
	if EmptyIndex < 7 then -- Can move down
		table.insert(Openers, {'D', swapElements(State, EmptyIndex, EmptyIndex + 3)})
	end

	return Openers
end

local function goalDistance(OpenList)
	local State = getState(OpenList[1])
	local Score = 9
	for i, v in ipairs(State) do
		if State[i] == CurrentGoalState[i] then
			Score -= 1
		end
	end
	return Score
end

local function travelDistance(OpenList)
	return #OpenList - 1
end

local function findBestScore(Queue)
	local BestScore = nil
	local Holder = nil
	local Index = nil

	for i, v in ipairs(Queue) do
		local score = goalDistance(v[1]) + travelDistance(v[1])
		if not BestScore or score <= BestScore then
			BestScore = score
			Holder = v[1]
			Index = i
		end
	end
	return Index
end

local function makeOpenInit(State)
	return {{{'nil', State}}}
end

local function extendPath(Path) -- Returns list of all possible moves out of path
	local Root = Path[1]
	local Moves = moves(getState(Root))
	Moves = removeRedundant(Moves, Path)
	for i, v in ipairs(Moves) do
		Moves[i] = {v, table.unpack(Path)}
	end

	return removeRedundant(Moves, Path)
end

local function moveTiles(NewState)
	for i, v in ipairs(TileFrames) do
		TweenService:Create(v, TileTweenInfo, {Position = TilePositions[table.find(NewState, i)]}):Play()
	end
	task.wait(TileTweenInfo.Time)
end

local function updatePuzzleImage(ImageId)
	local FormattedId = "rbxassetid://" .. ImageId
	for _, Image in ipairs(TileImages) do
		Image.Image = FormattedId
	end
end

--// Solve Functions

function ComputeFunctions.BFS(OpenList) -- Breadth First Search
	local Queue = {OpenList}
	BatchYields = 0
	while #Queue > 0 do
		if os.clock() - CurrentBatch > BatchSize then
			BatchYields += task.wait()
			CurrentBatch = os.clock()
		end
		if goalState(getState(Queue[1][1][1])) then
			return Queue[1][1]
		else
			local Extentions = extendPath(Queue[1][1])
			for i, v in ipairs(Extentions) do
				table.insert(Queue, {v})
			end

			table.remove(Queue, 1)
		end
	end
	return nil
end

function ComputeFunctions.DFS(OpenList, DepthBound) -- Depth First Search
	DepthBound = DepthBound or 5
	local Queue = {OpenList}
	BatchYields = 0
	while #Queue > 0 do
		if os.clock() - CurrentBatch > BatchSize then
			BatchYields += task.wait()
			CurrentBatch = os.clock()
		end
		if goalState(getState(Queue[1][1][1])) then
			return Queue[1][1]
		else
			local Extentions = extendPath(Queue[1][1])
			for i, v in ipairs(Extentions) do
				if #Queue[1][1] < DepthBound then
					table.insert(Queue, 2, {v})
				end
			end
			table.remove(Queue, 1)
		end
	end
	return nil
end

function ComputeFunctions.IDS(OpenList) -- Iterative Deepening
	local Queue = {OpenList}
	local Depth = 1
	BatchYields = 0
	while #Queue > 0 do
		if os.clock() - CurrentBatch > BatchSize then
			BatchYields += task.wait()
			CurrentBatch = os.clock()
		end
		if goalState(getState(Queue[1][1][1])) then
			return Queue[1][1]
		else
			local Extentions = extendPath(Queue[1][1])
			if #Queue[1][1] < Depth then
				Depth +=1
			end
			for i, v in ipairs(Extentions) do
				if #Queue[1][1] < Depth then
					table.insert(Queue, 2, {v})
				else
					table.insert(Queue, {v})
				end
			end
			table.remove(Queue, 1)
		end
	end
	return nil
end

function ComputeFunctions.AStar(OpenList)
	local Queue = {OpenList}
	BatchYields = 0
	while #Queue > 0 do
		if os.clock() - CurrentBatch > BatchSize then
			BatchYields += task.wait()
			CurrentBatch = os.clock()
		end
		local Index = findBestScore(Queue)
		if goalState(getState(Queue[Index][1][1])) then
			return Queue[1][Index]
		else
			local Extentions = extendPath(Queue[Index][1])
			for i, v in ipairs(Extentions) do
				if goalState(getState(v[1])) then
					return v
				else
					table.insert(Queue, {v})
				end
			end
			table.remove(Queue, Index)
		end
	end
	return nil
end

--// Event Functions

local LastImageText = ""
local function imageTextBoxChanged() -- Did this instead of string.sub because I wanted this behavior specifically
	local FilteredText = ImageTextBox.Text:gsub("%D+", "")
	if #FilteredText > 12 then
		ImageTextBox.Text = LastImageText
	else
		ImageTextBox.Text = FilteredText
		LastImageText = FilteredText
	end
end

local function imageTextBoxFocusLost(Valid)
	if Valid ~= false then
		updatePuzzleImage(ImageTextBox.Text)	
	end
end

local function compute()
	if Solving or not IsSolvable(CurrentState) then return end
	Solving = true
	local OpenInitiator = makeOpenInit(CurrentState)
	local Algorithm = ComputeFunctions[CurrentAlgorithm]
	
	local StartOs = os.clock()
	local Path = Algorithm(OpenInitiator)
	local Time = os.clock() - StartOs
	AlgorithmComputeLabel.Text = "Compute Time: " .. (Time - BatchYields) * 1000 .. " ms"
	CurrentState = CurrentGoalState
	for Move = #Path, 1, -1 do
		moveTiles(getState(Path[Move]))
	end
	Solving = false
end

local function changeAlgorithm(Algorithm)
	CurrentAlgorithm = Algorithm
	
	BFSButton.BackgroundColor3 = UNPICKED_COLOR
	DFSButton.BackgroundColor3 = UNPICKED_COLOR
	IDSButton.BackgroundColor3 = UNPICKED_COLOR
	AStarButton.BackgroundColor3 = UNPICKED_COLOR
	Frame[Algorithm].BackgroundColor3 = PICKED_COLOR
end

local function inputBegan(Input, GameProcessed)
	if GameProcessed or Solving or not ValidKeyCodes[Input.KeyCode] then return end
	
	for _, v in ipairs(moves(CurrentState)) do
		if getDirection(v) == ValidKeyCodes[Input.KeyCode] then
			CurrentState = getState(v)
			moveTiles(CurrentState)
			break
		end
	end
end

local function scramble()
	if Solving then return end
	CurrentState = getScrambledPuzzle()
	moveTiles(CurrentState)
end

moveTiles(CurrentState)

--// Events

SolveButton.MouseButton1Click:Connect(compute)
ScrambleButton.MouseButton1Click:Connect(scramble)

BFSButton.MouseButton1Click:Connect(function() changeAlgorithm("BFS") end) -- Ugly I know :(
DFSButton.MouseButton1Click:Connect(function() changeAlgorithm("DFS") end) 
IDSButton.MouseButton1Click:Connect(function() changeAlgorithm("IDS") end)
AStarButton.MouseButton1Click:Connect(function() changeAlgorithm("AStar") end)

ImageTextBox.FocusLost:Connect(imageTextBoxFocusLost)
ImageGoButton.MouseButton1Click:Connect(imageTextBoxFocusLost)
ImageTextBox:GetPropertyChangedSignal("Text"):Connect(imageTextBoxChanged)

UserInputService.InputBegan:Connect(inputBegan)
