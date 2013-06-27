package Caller_Of_Across_Compilation_Units is
   --  Function Min is a local function that returns
   --  the minimum of two natural numbers.

   function Min (X, Y: Natural) return Natural;

   --  Function Coprime determines if two natural
   --  number are coprime. It calls function Prime of
   --  package across_compilation_units in the process.

   function Coprime (X, Y: Natural) return Boolean;
end Caller_Of_Across_Compilation_Units;
