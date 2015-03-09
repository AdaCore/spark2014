package Inher is
    type Root_DIC_OK is tagged private with
      Default_Initial_Condition;
    type Child_DIC_KO is new Root_DIC_OK with private;
    --  no error stating that Child does not define full initial condition
private
    type Root_DIC_OK is tagged record
       F1 : Integer := 1;
    end record;

    type Child_DIC_KO is new Root_DIC_OK with record
       F2 : Integer;
    end record;
end Inher;
