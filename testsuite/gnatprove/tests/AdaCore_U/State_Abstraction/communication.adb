package body Communication with SPARK_Mode,
   Refined_State => (State => Ring_Buffer.Max) is
   function  Create  (Address : String; Port : Natural) return Mailbox is
   begin
      return (Address, Port, others => <>);
   end Create;
   procedure Send    (Message :     Data; To : in out Mailbox) is
   begin
      Ring_Buffer.Enqueue (Message, To.In_Buffer);
   end Send;
   procedure Receive (Message : out Data; To : in out Mailbox)is
   begin
      Ring_Buffer.Dequeue (Message, To.Out_Buffer);
   end Receive;
   package body Ring_Buffer  is
      procedure Enqueue (E :     Data; B : in out Buffer) is
      begin
         if B.Length >= Max then
            B.Content (B.First) := E;
            B.First := B.First + 1;
         elsif B.First + B.Length >= Max then
            B.Content (B.First + B.Length - Max) := E;
            B.Length := B.Length + 1;
         else
            B.Content (B.First + B.Length) := E;
            B.Length := B.Length + 1;
         end if;
      end Enqueue;

      procedure Dequeue (E : out Data; B : in out Buffer) is
      begin
         if B.Length = 0 then
            E := 0;
         elsif B.First >= Max then
            E := B.Content (B.First);
            B.Length := B.Length - 1;
            B.First := 1;
         else
            E := B.Content (B.First);
            B.Length := B.Length - 1;
            B.First := B.First + 1;
         end if;
      end Dequeue;
   end Ring_Buffer;
end Communication;
