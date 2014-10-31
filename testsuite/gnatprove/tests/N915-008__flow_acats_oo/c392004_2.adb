
----------------------------------------------------------------------------

with Report;
package body C392004_2 is

  procedure Create( The_Car : out Car; TC_Flag : Natural ) is
  begin
    case TC_Flag is
      when 2      => null; -- expected flag for this subprogram
      when others => Report.Failed ("Called Car Create");
    end case;
    C392004_1.Create( C392004_1.Vehicle(The_Car), 1);
    The_Car.Convertible := False;
  end Create;

  procedure Create( The_Limo : out Limo; TC_Flag : Natural ) is
  begin
    case TC_Flag is
      when 3      => null; -- expected flag for this subprogram
      when others => Report.Failed ("Called Limo Create");
    end case;
    C392004_1.Create( C392004_1.Vehicle(The_Limo), 1);
    The_Limo.Convertible := True;
 end Create;

end C392004_2;
