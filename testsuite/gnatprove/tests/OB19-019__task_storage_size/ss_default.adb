package body SS_Default is

    task body TT is
       X : Boolean := False;
    begin
       loop
          X := not X;
       end loop;
    end;

end;
