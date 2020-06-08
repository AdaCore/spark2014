pragma SPARK_Mode;
with RFLX.Generic_Types;
with RFLX.Builtin_Types;

package RFLX.Types is new RFLX.Generic_Types (Builtin_Types.Index, Builtin_Types.Byte, Builtin_Types.Bytes, Builtin_Types.Bytes_Ptr);
