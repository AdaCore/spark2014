pragma SPARK_Mode;

package body P is

  procedure Help_Doing_Nothing with No_Return;

  procedure Help_Doing_Nothing is
  begin
     loop
        null;
     end loop;
  end Help_Doing_Nothing;

  procedure Do_Nothing is
  begin
     Dummy := 0;
     Help_Doing_Nothing;
  end Do_Nothing;

  procedure Do_Something is
  begin
     Dummy := 0;
     Help_Doing_Nothing;
  end Do_Something;

end P;
