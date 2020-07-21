package P is
   type T is private with Default_Initial_Condition;
private
   type Mixed is record
      C1 : Integer := 0;
      C2 : Integer;
   end record;
   --  Type with mixed default initialization

   type T is record
      C : Mixed := Mixed'(C1 => 0, C2 => 0);
      --  Default expression overrides mixed initialization
   end record;
end;
