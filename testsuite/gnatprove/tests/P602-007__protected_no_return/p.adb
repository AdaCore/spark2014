pragma SPARK_Mode;

package body P is

  procedure Do_Nothing is
  begin
     loop
        null;
     end loop;
  end;

  protected body PT is
     procedure Do_Nothing is
     begin
        loop
           null;
        end loop;
     end;
  end PT;

  procedure Do_Something1 is
  begin
     Do_Nothing;
  end;

  procedure Do_Something2 is
  begin
     PO.Do_Nothing;
  end;

end P;
