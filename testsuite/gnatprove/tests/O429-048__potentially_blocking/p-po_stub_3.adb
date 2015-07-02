separate (P)
protected body PO_Stub_3 is
   entry Indirectly_Blocking_Stub_Entry when True is
   begin
      Blocking_Proc;
   end Indirectly_Blocking_Stub_Entry;

   procedure Indirectly_Blocking_Stub_Proc is
   begin
      Blocking_Proc;
   end Indirectly_Blocking_Stub_Proc;
end PO_Stub_3;
