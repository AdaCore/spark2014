package Gen with SPARK_Mode is

  type Ar is array (Integer range <>) of Integer;

  function Read (X : Integer) return Ar;

  generic
    with procedure Read (Buffer : Ar; X : out Integer);
    with function Pre (Buffer : Ar) return Boolean;
  function F return Integer
    with Pre => Pre (Read (10));
end Gen;
