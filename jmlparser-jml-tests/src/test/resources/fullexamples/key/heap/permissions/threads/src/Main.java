public class Main {

        /*@ normal_behavior
            requires this == \dl_currentThread();
            requires \permission(buf.inp) == \dl_initFullPermission();
            requires \permission(buf.outa) == \dl_initFullPermission();
            requires \permission(buf.outb) == \dl_initFullPermission(); @*/
        public /*@ helper @*/ void main(Buffer buf) {
           // possibly create buffer, requires not needed then
           Sampler sampler = new Sampler(buf);
           AFilter af = new AFilter(sampler, buf);
           BFilter bf = new BFilter(sampler, buf);
           Plotter p = new Plotter(af, bf, buf);
                // buf.inp =  { [ct] }
                // buf.outa = { [ct] }
                // buf.outb = { [ct] }
           sampler.start();
                // buf.inp = { [sampler, ct] }
           af.start();
                // buf.inp  = { [sampler, af, ct], [sampler, ct] }
                // buf.outa = { [af, ct] }
                // buf.outb = { [ct] }
           bf.start();
                // buf.inp = { [sampler, af, ct], [sampler, bf, ct] }
                // buf.outa = { [af, ct] }
                // buf.outb = { [bf, ct] }
           p.start();
                // buf.inp =  { [sampler, af, p, ct], [sampler, bf, p, ct] }
                // buf.outa = { [af, p, ct] }
                // buf.outb = { [bf, p, ct] }
           p.join();
                // buf.inp =  { [ct], [ct] }
                // buf.outa = { [ct] }
                // buf.outb = { [ct] }
           buf.inp = 0;
           buf.outa = 0;
           buf.outb = 0;
        }
}

