local player = game.Players.LocalPlayer

local gui = Instance.new("ScreenGui")
gui.Name = "KeyUI"
gui.ResetOnSpawn = false
gui.Parent = player:WaitForChild("PlayerGui")

-- Frame principal
local frame = Instance.new("Frame")
frame.Size = UDim2.new(0, 280, 0, 170)
frame.Position = UDim2.new(0.5, -140, 0.5, -85)
frame.BackgroundColor3 = Color3.fromRGB(20,20,20)
frame.Active = true
frame.Parent = gui

-- Bordes redondeados
local corner = Instance.new("UICorner")
corner.CornerRadius = UDim.new(0, 12)
corner.Parent = frame

-- Borde (UIStroke)
local stroke = Instance.new("UIStroke")
stroke.Thickness = 2
stroke.Color = Color3.fromRGB(80,80,80)
stroke.Parent = frame

-- Título
local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, 0, 0, 40)
title.Text = "Murder Vs Sheriff"
title.Font = Enum.Font.GothamBold
title.TextSize = 18
title.TextColor3 = Color3.fromRGB(255,255,255)
title.BackgroundTransparency = 1
title.Parent = frame

-- Input
local textbox = Instance.new("TextBox")
textbox.Size = UDim2.new(0.8, 0, 0, 35)
textbox.Position = UDim2.new(0.1, 0, 0.4, 0)
textbox.PlaceholderText = "Enter key..."
textbox.Text = ""
textbox.BackgroundColor3 = Color3.fromRGB(35,35,35)
textbox.TextColor3 = Color3.fromRGB(255,255,255)
textbox.Font = Enum.Font.Gotham
textbox.TextSize = 14
textbox.Parent = frame

local tbCorner = Instance.new("UICorner")
tbCorner.CornerRadius = UDim.new(0, 8)
tbCorner.Parent = textbox

-- Botón
local button = Instance.new("TextButton")
button.Size = UDim2.new(0.5, 0, 0, 35)
button.Position = UDim2.new(0.25, 0, 0.75, 0)
button.Text = "Enter"
button.Font = Enum.Font.GothamBold
button.TextSize = 14
button.BackgroundColor3 = Color3.fromRGB(60,130,255)
button.TextColor3 = Color3.new(1,1,1)
button.Parent = frame

local btnCorner = Instance.new("UICorner")
btnCorner.CornerRadius = UDim.new(0, 8)
btnCorner.Parent = button

-- Drag PC + móvil
local dragging = false
local dragInput, dragStart, startPos

frame.InputBegan:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseButton1 
	or input.UserInputType == Enum.UserInputType.Touch then
		dragging = true
		dragStart = input.Position
		startPos = frame.Position

		input.Changed:Connect(function()
			if input.UserInputState == Enum.UserInputState.End then
				dragging = false
			end
		end)
	end
end)

frame.InputChanged:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseMovement 
	or input.UserInputType == Enum.UserInputType.Touch then
		dragInput = input
	end
end)

game:GetService("UserInputService").InputChanged:Connect(function(input)
	if input == dragInput and dragging then
		local delta = input.Position - dragStart
		frame.Position = UDim2.new(
			startPos.X.Scale,
			startPos.X.Offset + delta.X,
			startPos.Y.Scale,
			startPos.Y.Offset + delta.Y
		)
	end
end)

-- Acción botón
button.MouseButton1Click:Connect(function()
	local key = textbox.Text
	print("Key:", key)
end)
