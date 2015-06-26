separate (P)
protected body PO_Stub_2 is
   entry Blocking_Entry when True is
   begin
      delay until Now;
   end Blocking_Entry;
end PO_Stub_2;
