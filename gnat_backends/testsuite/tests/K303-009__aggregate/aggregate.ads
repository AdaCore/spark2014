package aggregate is
   type TemplatePadI is range 1..452;
   type TemplatePadT is array(TemplatePadI) of Integer;

   NullTemplatePad : constant TemplatePadT
     := TemplatePadT'(others => 0);

   procedure A ( X : Integer);

end aggregate;
