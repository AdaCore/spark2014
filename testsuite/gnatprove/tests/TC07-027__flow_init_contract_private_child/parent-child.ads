private package Parent.Child with Abstract_State => (B with Part_Of => A) is
   procedure Dummy with Global => null;  -- just to force a refinement
end Parent.Child;
