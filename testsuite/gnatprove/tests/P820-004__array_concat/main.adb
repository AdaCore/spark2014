procedure main with SPARK_Mode is
   vstring : constant String := Integer'Image (10); -- unconstrained type ... lower bound not fixed.

   pragma Assert (Integer'Size <= 32);
   pragma Assume (vstring'Length <= 11 and vstring'Length > 0);

   cs : constant String (1..2) := (others => ' ');

   --  concat with unconstrained:
   catstring   : constant String := vstring & vstring & vstring;   -- unconstrained, verification fail -> ok
   catstring1  : constant String := (vstring & vstring) & vstring; -- unconstrained, verification success -> ?
   catstring2  : constant String := vstring & (vstring & vstring); -- unconstrained, verification success -> ?

   --  concat with constrained:
   catstring8  : constant String := vstring & cs & vstring;        -- unconstrained, verification fail -> ok
   catstring9  : constant String := (vstring & cs) & vstring;      -- unconstrained, verification success -> ?
   catstring10 : constant String := vstring & (cs & vstring);      -- unconstrained, verification success -> ?

   --  concat with string literals:
   catstring3 : constant String := vstring & " hello" & vstring;   -- unconstrained, verification fail -> ok
   catstring4 : constant String := (vstring & " hello") & vstring; -- unconstrained, but verification success -> ?
   catstring5 : constant String := vstring & (" hello" & vstring); -- unconstrained, but verification success -> ?
   catstring6 : constant String := "hello" & vstring & "hello";    -- internally constrained by constant string -> ?

   pragma Assert (vstring'First <= 1);
begin
   null;
end main;
