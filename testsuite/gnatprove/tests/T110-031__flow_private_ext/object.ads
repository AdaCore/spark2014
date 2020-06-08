package Object is
   type T is abstract tagged private with Default_Initial_Condition;
private
   type T is abstract tagged record
      Area : Integer := -1;  -- set to -1 if not yet computed
   end record;
end Object;
