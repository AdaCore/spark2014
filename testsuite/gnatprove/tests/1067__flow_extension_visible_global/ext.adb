procedure Ext is

   type Root_T is tagged null record;

   procedure Outer (A : Root_T)
   with Global => null,
        Extensions_Visible
   is
      procedure Inner
      with Global => A
      is
      begin
         null;
      end Inner;
   begin
      null;
   end Outer;

begin
   null;
end Ext;
