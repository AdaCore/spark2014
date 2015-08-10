separate (P)
protected body PO_Stub_2 is
   entry Directly_Blocking_Stub_Entry when True is
   begin
      delay until Now;
   end Directly_Blocking_Stub_Entry;

   procedure Directly_Blocking_Stub_Proc is
   begin
      delay until Now;
   end Directly_Blocking_Stub_Proc;
end PO_Stub_2;
