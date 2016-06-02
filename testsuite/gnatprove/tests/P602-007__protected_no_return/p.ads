pragma SPARK_Mode;

package P is

  procedure Do_Nothing with No_Return;

  protected type PT is
     procedure Do_Nothing with No_Return;
  end PT;

  PO : PT;

  procedure Do_Something1 with Pre => True;
  procedure Do_Something2 with Pre => True;

end P;
