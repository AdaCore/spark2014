package P is
   X : Boolean := True;

   procedure Explicit with Global => (In_Out => X);
   procedure Implicit;
   --  Subprograms with explicit and generated globals, respectively

   type Callback is access procedure;

   Explicit_Callback : Callback := Explicit'Access;
   Implicit_Callback : Callback := Implicit'Access;
end;
