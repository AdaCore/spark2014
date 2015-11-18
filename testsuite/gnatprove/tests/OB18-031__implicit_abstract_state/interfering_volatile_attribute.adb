package body Interfering_Volatile_Attribute is

    task body T is
       X : Boolean := False;
    begin
       X := not X;
    end;

end;
