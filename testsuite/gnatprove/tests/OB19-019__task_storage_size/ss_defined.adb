package body SS_Defined is

    task body TT1 is
       X : Boolean := False;
    begin
       loop
          X := not X;
       end loop;
    end;

    task body TT2 is
       X : Boolean := False;
    begin
       loop
          X := not X;
       end loop;
    end;

end;
