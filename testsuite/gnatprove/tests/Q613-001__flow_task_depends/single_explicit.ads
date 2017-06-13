with Tasking; use Tasking;

package Single_Explicit is

   task Worker
     with Global  => (In_Out => Mailbox),
          Depends => (Mailbox =>+ null, Worker =>+ null);

end;
