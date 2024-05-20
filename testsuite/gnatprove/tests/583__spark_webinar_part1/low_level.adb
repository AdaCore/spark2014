pragma Warnings (Off, "analyzing unreferenced");
with Ada.Unchecked_Conversion;
with Rich_Data; use Rich_Data;

package body Low_Level
    with SPARK_Mode
is
    -- Untyped memory manipulations

    type C_Struct is
    record
        A : Integer;
        B : Character;
        C : Storage_Element;
        D : Short_Integer;
    end record;
    --  with Alignment => 4, Size => 64, Object_Size => 64;

    type Buffer is array (1 .. 8) of Storage_Element;
    --  with Pack;

    function Convert is new Ada.Unchecked_Conversion (Source => Buffer, Target => C_Struct);

    procedure Erase (Arg : aliased in out C_Struct) is
        Buf : Buffer
        with Import, Address => Arg'Address;
    begin
        for I in Buffer'Range loop
            Buf (I) := 0;
        end loop;
    end Erase;

    -- Software/Hardware interactions

    pragma Warnings (GNATprove, Off, "address specification * is imprecisely supported");
    Var :
        Integer
        --  Small_Int
    with
        --  Volatile,
        --  Atomic,
        --  Async_Writers,
        --  Async_Readers,
        --  Effective_Writes,
        --  Effective_Reads,
        Address => To_Address (16#0ADA_ADA0#);

    -- Bindings with C

    -- Type C_Struct maps to C type:
    --
    --  typedef struct {
    --    int a;
    --    char b;
    --    unsigned char c;
    --    short d;
    --  } c_struct;

    procedure Update_C_Struct (Arg : in out C_Struct)
    with
        Convention => C,
        Import,
        External_Name => "update_c_struct",
        Global => null,
        Always_Terminates;
    -- Binds to C function
    -- void update_c_struct (c_struct* arg);

    function Read_C_Struct (Arg : C_Struct) return Integer
    with
        Convention => C,
        Export,
        External_Name => "read_c_struct";
    -- Binds to C declaration
    -- int read_c_struct (c_struct* arg);

    procedure Init (Arg : in out C_Struct)
    with
        Convention => C,
        Export,
        External_Name => "init";

    function Read_C_Struct (Arg : C_Struct) return Integer is
    begin
        return Arg.A;
    end Read_C_Struct;

    procedure Init (Arg : in out C_Struct) is
    begin
       Update_C_Struct (Arg);
    end;

end Low_Level;
