procedure Test_Delta_Record with SPARK_Mode is
   type Simple is record
      F1, F2 : Integer;
   end record;

   type With_Discr (D : Boolean) is record
      case D is
      when True =>
         F1, F2 : Integer;
      when False =>
         G1, G2 : Integer;
      end case;
   end record;

   procedure Test_Simple with Pre => True is
      X : Simple := (1, 2);
   begin
      X := (X with delta F1 => 2);
      pragma Assert (X = (2, 2));
   end Test_Simple;

   procedure Test_Discr with Pre => True is
      X : With_Discr (True) := (True, 1, 2);
   begin
      X := (X with delta F1 => 2);
      pragma Assert (X = (True, 2, 2));
   end Test_Discr;
begin
   null;
end Test_Delta_Record;
