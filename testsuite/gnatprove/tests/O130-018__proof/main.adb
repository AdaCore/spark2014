procedure Main is
   type Array_Type is array (Natural range <>) of Integer;

   type Branch_Type (M_Height : Natural) is
      record
         M_Nodes           : Array_Type (0 .. M_Height);
      end record;

   pragma Warnings (Off, "analyzing unreferenced procedure");
   procedure Create_Empty_Branch
     (Branch : out Branch_Type)
   is
   begin
      Branch.M_Nodes := (others => 0);

      for I in Branch.M_Nodes'Range loop
         pragma Loop_Invariant
           (I in Branch.M_Nodes'Range and
              Branch.M_Nodes'First = Branch'Loop_Entry.M_Nodes'First and
              Branch.M_Nodes'Last  = Branch'Loop_Entry.M_Nodes'Last);

         if I = Branch.M_Nodes'Last then
            pragma Assert (I in Branch.M_Nodes'Range);
            Branch.M_Nodes (
                            I          --@INDEX_CHECK:PASS
                           ) := 0;
         end if;
      end loop;
   end Create_Empty_Branch;

begin
   null;
end Main;
