with Queries; use Queries;

procedure Test with SPARK_Mode is
   X : R with Potentially_Invalid;
begin
   Field_Query (X);
   pragma Assert (X.F'Valid);
   X := Make;
   pragma Assert (X.F'Valid);
end Test;
