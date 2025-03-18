--import all worlds
import Game.Levels.TutorialWorld
import Game.Levels.DeterminantWorld
import Game.Levels.MatrixWorld

-- Here's what we'll put on the title screen
Title "A Lean4 Game of Linear Algebra"
/-Introduction
"
This text appears on the starting page where one selects the world/level to play.
You can use markdown.
"-/
Introduction
"
你是否对线性代数感到头疼？是否想要一种全新的方式来学习数学？那么，欢迎来到 Lean 线性代数世界！

在这里，你将不再是枯燥地面对公式和定理，而是化身为一位数学探险家，运用 Lean 强大的定理证明功能，解决一道道精心设计的线性代数谜题。
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use markdown.
"

/-! Information to be displayed on the servers landing page. -/
Languages "Chinese"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
