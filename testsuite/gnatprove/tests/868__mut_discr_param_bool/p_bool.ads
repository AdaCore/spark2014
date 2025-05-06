package P_Bool is

   type T (K1 : Boolean := False) is record
      null;
   end record;

   procedure Proc1 (Rec : in out T);

   procedure Proc2 (Rec : out T);

end P_Bool;
