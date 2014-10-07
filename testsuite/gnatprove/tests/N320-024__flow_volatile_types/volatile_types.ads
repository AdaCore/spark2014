package Volatile_Types is
   type Volatile_Type is range 1 .. 10
     with Volatile;

   subtype Volatile_Subtype is Volatile_Type range 1 .. 5;

   Vol : Volatile_Subtype
     with Async_Writers,
          Effective_Reads;

   procedure Good_Read (Value : out Integer)
     with Global => (In_Out => Vol);  --  OK

   procedure Bad_Read (Value : out Integer)
     with Global => Vol;  --  Problem!!! Vol has Effective_Reads so it
                          --  has to be In_Out.

   procedure Local_Vol (Value : out Integer);
end Volatile_Types;
