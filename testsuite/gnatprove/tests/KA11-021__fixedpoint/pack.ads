package Pack is
   type Volt is delta 0.125 range -128.0 .. 127.0;

   Default_V : Volt := -0.125;

   type Money is delta 0.01 digits 15;
   subtype Salary is Money digits 10;

   Init_Stash     : constant Money := 10000.0;
   Init_Pocket    : constant Money := Money (0.0);
   Default_Salary : constant Salary := Salary (Init_Pocket);

   Stash  : Money := Init_Stash;
   Pocket : Money := Init_Pocket;

   procedure Get_Paid (S : Salary := Default_Salary)
     with Pre  => (S > 0.0),
          Post => (Stash + Pocket = Stash'Old + Pocket'Old);

end Pack;
