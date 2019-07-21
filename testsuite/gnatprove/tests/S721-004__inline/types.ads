package Types is
   type Node_Id is new Integer;
   subtype Entity_Id is Node_Id;
   Empty : constant Node_Id := 0;

   function Stream_Attribute_Available
     (Typ : Entity_Id) return Boolean;

end Types;
