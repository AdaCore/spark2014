package Pre_Post_Exercise with SPARK_Mode is

    function Is_Full return Boolean with
      Post => Is_Full'Result = (Model'Length >= 100);
    function Is_Empty return Boolean with
      Post => Is_Empty'Result = (Model'Length = 0);

    procedure Push (X : in Integer) with
      Pre => not Is_Full,
      Post => Model = Model'Old & (1 => X);

    procedure Pop (X : out Integer) with
      Pre => not Is_Empty,
      Post => Model & (1 => X) = Model'Old;

    type Int_Arr is array (Positive range <>) of Integer;

    function Model return Int_Arr with Ghost,
      Post => Model'Result'First = 1;

end Pre_Post_Exercise;
