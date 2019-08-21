package body Sem_Cat is

   function Simply_False return Boolean is
   begin
      return False;
   end Simply_False;

   procedure Validate_RT_RAT_Component (N : Node_Id) is
      Typ : Entity_Id := Empty;

      function Stream_Attributes_Available (Typ : Entity_Id) return Boolean is
      begin
         return Stream_Attribute_Available (Empty);
      end Stream_Attributes_Available;

   begin
      if True
        or else (Stream_Attributes_Available (Typ)
                 and then Simply_False)
      then
         null;
      end if;
   end Validate_RT_RAT_Component;

end Sem_Cat;
