package P_Int is

   type T (K : Integer := 555) is record
      null;
   end record;

   procedure Proc1 (Rec : in out T);

   procedure Proc2 (Rec : out T);

end P_Int;
