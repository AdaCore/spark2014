
----------------------------------------------------------------------------

with C392004_1;
package C392004_2 is

  type Car is new C392004_1.Vehicle with record
    Convertible : Boolean;
  end record;

  -- masking definition
  procedure Create( The_Car : out Car; TC_Flag : Natural );

  type Limo is new Car with null record;

  procedure Create( The_Limo : out Limo; TC_Flag : Natural );

end C392004_2;
