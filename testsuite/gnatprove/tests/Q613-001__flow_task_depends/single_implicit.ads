with Tasking; use Tasking;

package Single_Implicit is

   task Worker
     with Global  => (In_Out => Mailbox),
          Depends => (Mailbox =>+ null);

end;
