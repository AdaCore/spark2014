procedure Side with SPARK_Mode is
   function Flip (X : in out Boolean) return String
     with Side_Effects
   is
   begin
      X := not X;
      return "abc";
   end;

   V : Boolean;

begin
   V := True;
   S : String := Flip (V);
end;
