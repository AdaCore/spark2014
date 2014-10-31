
package body C392004_1 is
  procedure Create ( The_Vehicle : out Vehicle; TC_Flag : Natural ) is
  begin
    case TC_Flag is
      when 1 => null; -- expected flag for this subprogram
      when others =>
         Report.Failed ("Called Vehicle Create");
    end case;
    The_Vehicle := (Engine_On => False);
  end Create;

  procedure Start ( The_Vehicle : in out Vehicle ) is
  begin
    The_Vehicle.Engine_On := True;
  end Start;

end C392004_1;
