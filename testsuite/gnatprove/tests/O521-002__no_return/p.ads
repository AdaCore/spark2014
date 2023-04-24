pragma SPARK_Mode;

package P is

  Dummy : Integer;

  procedure Do_Nothing with No_Return, Global => null, Exceptional_Cases => (others => False);

  procedure Do_Something with Global => null;

end P;
