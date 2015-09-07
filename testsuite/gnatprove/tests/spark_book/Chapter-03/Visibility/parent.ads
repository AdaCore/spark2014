package Parent is
   type Parent_Int is private;
   procedure Square (Value : in out Parent_Int);
private
   type Parent_Int is new Integer;
   P : constant Parent_Int := 27;
end Parent;
