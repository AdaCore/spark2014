pragma SPARK_Mode;

package P is

  Dummy : Integer;

  procedure Do_Nothing with No_Return, Global => null;

  procedure Do_Something with Global => null;

end P;
