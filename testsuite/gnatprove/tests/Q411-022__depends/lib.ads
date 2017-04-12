package Lib is

  protected type AA is
     entry Insert (An_Item : in out Integer) with
       Depends => (An_Item => null, AA => An_Item);
  private
     S:Integer := 0;
  end AA;

end Lib;
