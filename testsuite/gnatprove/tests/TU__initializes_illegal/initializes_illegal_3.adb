package body Initializes_Illegal_3
  with Refined_State => (S1 => null,
                         S2 => null)
is
   package body Emb
     with Refined_State => (SS => null)
   is
   end Emb;
end Initializes_Illegal_3;
