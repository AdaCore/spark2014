with Interfaces.C; use Interfaces.C;

package A with SPARK_Mode is

   procedure Tcp_Receive (Data : out Char_Array)
      with
        Pre => Data'Last >= Data'First;

end A;
