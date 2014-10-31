
----------------------------------------------------------------------------

with Report;
with C392004_1; use C392004_1;
with C392004_2; use C392004_2;
procedure C392004 is

  My_Car : Car;
  Your_Car : Limo;

  procedure TC_Assert( Is_True : Boolean; Message : String ) is
  begin
    if not Is_True then
      Report.Failed (Message);
    end if;
  end TC_Assert;

begin  -- Main test procedure.

  Report.Test ("C392004", "Check subprogram inheritance & visibility " &
                          "for derived tagged types" );

  My_Car.Convertible := False;
  Create( Vehicle( My_Car ), 1 );
  TC_Assert( not My_Car.Convertible, "Altered descendent component 1");

  Create( Your_Car, 3 );
  TC_Assert( Your_Car.Convertible, "Did not set inherited component 2");

  My_Car.Convertible := True;
  Create( Vehicle( My_Car ), 1 );
  TC_Assert( My_Car.Convertible, "Altered descendent component 3");

  Create( My_Car, 2 );
  TC_Assert( not My_Car.Convertible, "Did not set extending component 4");

  My_Car.Convertible := False;
  Start( Vehicle( My_Car ) );
  TC_Assert( not My_Car.Convertible , "Altered descendent component 5");

  Start( My_Car );
  TC_Assert( not My_Car.Convertible, "Altered unreferenced component 6");

  Your_Car.Convertible := False;
  Start( Vehicle( Your_Car ) );
  TC_Assert( not Your_Car.Convertible , "Altered descendent component 7");

  Start( Your_Car );
  TC_Assert( not Your_Car.Convertible, "Altered unreferenced component 8");

  My_Car.Convertible := True;
  Start( Vehicle( My_Car ) );
  TC_Assert( My_Car.Convertible, "Altered descendent component 9");

  Start( My_Car );
  TC_Assert( My_Car.Convertible, "Altered unreferenced component 10");

  Report.Result;

end C392004;
