package body TTI is

    task body T is
       X : Boolean := False;
    begin
       loop
          X := not X;
       end loop;
    end;

end;
