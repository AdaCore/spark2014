with Ada.Text_IO;
with Bounded_Table;

procedure Repro_Main
is

   pragma Annotate (GNATprove, Terminating, Repro_Main);

   package Int_Table is new Bounded_Table
     (Elem_Type => Integer,
      Null_Elem => 0,
      Max       => 32);

   Table : Int_Table.T := Int_Table.Empty_Table;
begin
   Int_Table.Push (Table => Table, Elem => 2);
   Int_Table.Push (Table => Table, Elem => 3);
   Int_Table.Push (Table => Table, Elem => 5);
   Int_Table.Push (Table => Table, Elem => 7);
   Int_Table.Push (Table => Table, Elem => 11);

   for I in Table loop
      Ada.Text_IO.Put_Line (Int_Table.Element(Table, I)'Img);
      pragma Loop_Variant (Increases => Int_Table.Index_Of(I));
   end loop;

end Repro_Main;
