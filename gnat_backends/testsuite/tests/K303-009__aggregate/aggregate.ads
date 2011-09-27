package aggregate is
   type TemplatePadI is range 1..452;
   type TemplatePadT is array(TemplatePadI) of Integer;

   NullTemplatePad : constant TemplatePadT
     := (others => 0);

   procedure A (X : Integer; K : out TemplatePadT)
      with Pre  => (X = 1),
           Post => (K (1) = 2 and then K (11) = 2 and then K (6) = 1);

end aggregate;
