package body Lib is

  protected body AA is
     entry Insert (An_Item : in out Integer) when True is
     begin
        S := An_Item;
     end Insert;
  end AA;

end Lib;
