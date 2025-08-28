/*
 * (c) Copyright 2008 Yoshinori Toshima (Sun)
 */

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.RandomAccessFile;
import java.io.UnsupportedEncodingException;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.TreeMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author Yoshinori Toshima
 */
public class HprofConverter {
    private static final String versionString = "HprofConverter 0.2";
    private boolean verbose = false;
    private boolean dump_name = false;
    private boolean convert = false;
    private boolean dumpCharArray = false;
    private boolean dumpString = false;
    private Map charArrayMap = new TreeMap();
    private Map pendingStrings = new TreeMap();
    private List hprof_files = new ArrayList();
    private PrintWriter hprof_out = null;
    private Logger logger = Logger.getLogger(getClass().getName());
    private Map nameMap = new HashMap();
    private Map cnDic = new HashMap();
    private Map clsDic = new HashMap();
    private MappedByteBuffer buf;
    private int pointerSize;
    private long tms;
    private String currentPath;
    private String outfile_name;
    private int remaining;
    private int currentPass;
    private boolean includeHeaderSize = true;
    private long n_HPROF_GC_CLASS_DUMP;
    private long n_HPROF_GC_INSTANCE_DUMP;
    private long n_HPROF_GC_OBJ_ARRAY_DUMP;
    private long n_HPROF_GC_PRIM_ARRAY_DUMP;
    
    private static final String helpMessage = "usage: java -jar HprocConverter [-convert] [-v|-q] <binary hprof file...>\n"
            + "  HprocConverter converts hprof binary file to hprof ASCII file.\n"
            + "  Currently, it converts heapdump records only.\n"
            + "  Options:\n"
            + "    -convert: tell the tool to convert hprof to ASCII.\n"
            + "              Without this option, the tool simply parses input file(s).\n"
            + "    -dump_string: Dump Strings to stdout.\n"
            + "    -dump_char_array: Dump char array to stdout.\n"
            + "    -v: set logging level to FINER.  Cannot be used with -q\n"
            + "    -q: set logging level to WARNING.  Cannot be used with -v"; 
           
    
    private static final String loggingHelpMessage = "  For logging, specify following logging property by -Djava.util.logging.config.file.\n"
            + "    name.dolphin.duke.level = FINE\n"
            + "    java.util.logging.ConsoleHandler.level = FINE\n"
            + "    handlers= java.util.logging.ConsoleHandler\n";

    static void showHelp() {
        System.out.println(versionString);
        System.out.println(helpMessage);
    }

    private void processArgs(String[] args) {
        boolean vflag = false;
        boolean qflag = false;
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("-v")) {
                verbose = true;
                logger.setLevel(Level.FINER);
                ConsoleHandler ch = new ConsoleHandler();
                ch.setLevel(Level.FINER);
                logger.addHandler(ch);
                logger.fine("-v was used.");
                logger.info("logger: " + logger + " level " + logger.getLevel());
                vflag = true;
            } else if (args[i].equals("-q")) {
                logger.setLevel(Level.WARNING);
                ConsoleHandler ch = new ConsoleHandler();
                ch.setLevel(Level.WARNING);
                logger.addHandler(ch);                
                qflag = true;
            } else if (args[i].equals("-dump_name")) {
                dump_name = true;
            } else if (args[i].equals("-convert")) {
                convert = true;
            } else if (args[i].equals("-dump_char_array")) {
                dumpCharArray = true;
            } else if (args[i].equals("-dump_string")) {
                dumpString = true;
            } else if (args[i].equals("-h") || args[i].equals("-help")) {
                showHelp();
                System.exit(0);
            } else {
                hprof_files.add(args[i]);
            }
        }
        if (vflag & qflag) {
            logger.severe("-v and -q cannot be used at the same time.");
            System.exit(1);
        }
    }

    private void readHeader(boolean print) throws UnsupportedEncodingException {
        byte[] magic_str_bytes = new byte[19];
        buf.get(magic_str_bytes);

        byte[] magic_str_bytes1 = new byte[18];
        System.arraycopy(magic_str_bytes, 0, magic_str_bytes1, 0, 18);

        String magic = new String(magic_str_bytes1, "ASCII");
        if (print & logger.isLoggable(Level.INFO)) {
            System.out.println(magic);
        }
        pointerSize = buf.getInt();

        if (print & logger.isLoggable(Level.INFO)) {
            System.out.println("pointer size " + pointerSize);
        }

        tms = buf.getLong();

        Date ts = new Date(tms);
        if (print & logger.isLoggable(Level.INFO)) {
            System.out.println("ts " + ts + " " + Long.toHexString(tms));
        }

        if (magic_str_bytes[18] != 0) {
            logger.log(Level.SEVERE, "ERROR: file " + currentPath + " may not be a binary hprof file.");
            System.exit(1);
        }
    }

    private void setupOutput() throws IOException {

        outfile_name = currentPath + ".txt";
        File outfile = new File(outfile_name);
        if (outfile.exists()) {
            String prevname = outfile_name + ".prev";
            if (logger.isLoggable(Level.INFO)) {
                System.out.print("convert target file " + outfile_name + " already exists.");            
                System.out.print("renaming to " + prevname + "...");
            }
            File prevfile = new File(prevname);
            if (prevfile.exists()) {
                prevfile.delete();
            }
            if (outfile.renameTo(new File(prevname))) {
                if (logger.isLoggable(Level.INFO)) {
                    System.out.println(" OK");
                }
            } else {
                if (logger.isLoggable(Level.INFO)) {
                  System.out.println(" NG");
                }
                System.exit(2);
            }
        }

        if (logger.isLoggable(Level.INFO)) { 
            System.out.println("ASCII hprof output is " + outfile_name);
        }
        
        hprof_out = new PrintWriter(new FileWriter(outfile_name));
        hprof_out.println(ascii_hprof_header);
        hprof_out.println("HEAP DUMP BEGIN (0 objects, 0 bytes) Sun Mar  9 20:47:55 2008");
        hprof_out.flush();

    }

    private Id readId() {
        if (pointerSize == 4) {
            int v = buf.getInt();
            return new Id(0xffffffffL & v);
        } else if (pointerSize == 8) {
            long v = buf.getLong();
            return new Id(v);
        }
        throw new IllegalStateException("pointer_size " + pointerSize + " is invalid.");
    }

    private void process_UTF8() throws UnsupportedEncodingException {
        if (remaining < 4) {
            logger.log(Level.SEVERE, "WARN: remaining = " + remaining);
            return;
        }

        Id nameid = readId();

        String str = "";
        int balen = remaining - pointerSize;
        if (balen > 0) {
            int current_offset = buf.position();
            try {
                byte[] utf8a = new byte[remaining - pointerSize];
                buf.get(utf8a);
                str = new String(utf8a, "UTF8");
            } catch (OutOfMemoryError oome) {
                logger.log(Level.SEVERE, "OutOfMemoryError balen " + balen + ", current position " + Integer.toOctalString(current_offset));
                str = "__out_of_memory_error__";
            }
        }

        if (dump_name) {
            System.out.printf("name %x %s\n", nameid.getValue(), str);
        }
        nameMap.put(nameid, str);

    // test
    //long idval = nameid.getValue();
    //Id nid2 = new Id(idval);
    //System.out.println("nid2 ent " + nameMap.get(nid2) + " idval " + idval + " nid2.val " + nid2.getValue() + " mapsz " + nameMap.size());
    }

    private void process_LOAD_CLASS() {
        int serial = buf.getInt();
        Id objid = readId();
        int stktsn = buf.getInt();
        Id nameid = readId();
        logger.log(Level.FINE, String.format("class sn %x id %x stktn %x nid %x %s\n", serial, objid.getValue(), stktsn, nameid.getValue(), nameMap.get(nameid)));
        cnDic.put(objid, nameid);
    }

    private void process_HEAP_DUMP() {
        int endpos = buf.position() + remaining;
        long n_processed = 0;
        boolean printProgress = false;
        if (currentPass == 2 && logger.isLoggable(Level.INFO)) {
            if (dumpCharArray == false && dumpString == false) {
              System.out.println("Progress (. for 10000 records)");
              printProgress = true;
            }
        }
        while (buf.position() < endpos) {
            byte srt = buf.get();
            switch (srt) {
                case HPROF_GC_ROOT_UNKNOWN:
                    process_HPROF_GC_ROOT_UNKNOWN();
                    break;
                case HPROF_GC_ROOT_THREAD_OBJ:
                    process_HPROF_GC_ROOT_THREAD_OBJ();
                    break;
                case HPROF_GC_ROOT_JNI_GLOBAL:
                    process_HPROF_GC_ROOT_JNI_GLOBAL();
                    break;
                case HPROF_GC_ROOT_JNI_LOCAL:
                    process_HPROF_GC_ROOT_JNI_LOCAL();
                    break;
                case HPROF_GC_ROOT_JAVA_FRAME:
                    process_HPROF_GC_ROOT_JAVA_FRAME();
                    break;
                case HPROF_GC_ROOT_NATIVE_STACK:
                    process_HPROF_GC_ROOT_NATIVE_STACK();
                    break;
                case HPROF_GC_ROOT_STICKY_CLASS:
                    process_HPROF_GC_ROOT_STICKY_CLASS();
                    break;
                case HPROF_GC_ROOT_THREAD_BLOCK:
                    process_HPROF_GC_ROOT_THREAD_BLOCK();
                    break;
                case HPROF_GC_ROOT_MONITOR_USED:
                    process_HPROF_GC_ROOT_MONITOR_USED();
                    break;
                case HPROF_GC_CLASS_DUMP:
                    process_HPROF_GC_CLASS_DUMP();
                    break;
                case HPROF_GC_INSTANCE_DUMP:
                    process_HPROF_GC_INSTANCE_DUMP();
                    n_processed++;
                    break;
                case HPROF_GC_OBJ_ARRAY_DUMP:
                    process_HPROF_GC_OBJ_ARRAY_DUMP();
                    n_processed++;
                    break;
                case HPROF_GC_PRIM_ARRAY_DUMP:
                    process_HPROF_GC_PRIM_ARRAY_DUMP();
                    n_processed++;
                    break;
                default:
                    logger.log(Level.SEVERE, "Unknown heapdump sub record type " + srt);
                    System.exit(1);
            }
            if (printProgress) {
                if (((n_processed+1)%10000) == 0) {
                  System.out.print(".");
                  System.out.flush();
                }
            }
        }
        if (printProgress) {
            System.out.println("");           
        }
    }

    private void process_HPROF_GC_PRIM_ARRAY_DUMP() {
        String srn = "HPROF_GC_PRIM_ARRAY_DUMP";
        // println "HPROF_GC_PRIM_ARRAY_DUMP"
        // is and stack trace id
        Id id = readId();
        int stktrcsn = buf.getInt();
        int n_elements = buf.getInt();
        byte etype = buf.get();

        logger.log(Level.FINE, srn + " id " + id + " elms " + n_elements + " type " + etype);

        int sz = 0;
        String elem_type_s = "";
        switch (etype) {
            case 4: // boolean
                elem_type_s = "boolean";
                sz = n_elements;
                break;
            case 5: // char
                elem_type_s = "char";
                sz = n_elements * 2;
                break;
            case 6: // float
                elem_type_s = "float";
                sz = n_elements * 4;
                break;
            case 7: // double
                elem_type_s = "double";
                sz = n_elements * 8;
                break;
            case 8: // byte
                elem_type_s = "byte";
                sz = n_elements;
                break;
            case 9: // short
                elem_type_s = "short";
                sz = n_elements * 2;
                break;
            case 10: // int
                elem_type_s = "int";
                sz = n_elements * 4;
                break;
            case 11: // long
                elem_type_s = "long";
                sz = n_elements * 8;
                break;
            default:
                logger.log(Level.SEVERE, "Unexpected primitive array element type " + etype);
            }

        byte[] tbuf = new byte[sz];
        buf.get(tbuf);

        if (currentPass == 2 && etype == 5 ) {
          int calen = sz / 2;
          char[] ca = new char[calen];
          for (int i = 0; i < calen; i++) {
            ca[i] = (char)((0xff00 & (tbuf[i*2]<<8)) | (tbuf[i*2+1]&0xff));
          }

          if (dumpString) {
            // keep char array in a map
            charArrayMap.put(id, ca);
          }

          if (dumpCharArray) {
            String stmp = new String(ca);
            System.out.print(id.toHexString() + ": " + stmp);
            System.out.print(" // " + calen + " ");
            for (int i = 0; i < calen; i++) {
              System.out.print(Integer.toHexString(ca[i]) + " ");
            }
            System.out.println("");
            for (int i = 0; i < tbuf.length; i++) {
              System.out.print(Integer.toHexString(tbuf[i]) + " ");
            }
            System.out.println("");
          }
        }

        if (convert && currentPass == 2) {
            if (includeHeaderSize) {
                sz += pointerSize*2 + 4;
            }
            hprof_out.println("ARR " + id + " (sz=" + sz + ", trace=0, nelems=" + n_elements + ", elem type=" + elem_type_s + ")");
        //hprof_out.println "ARR ${Integer.toHexString(id)} (sz=${sz}, trace=0, nelems=${n_elements}, elem type=${elem_type_s})"
        }
        if (currentPass == 1) {
            n_HPROF_GC_PRIM_ARRAY_DUMP++;
        }
    }

    private void process_HPROF_GC_OBJ_ARRAY_DUMP() {
        String srn = "HPROF_GC_OBJ_ARRAY_DUMP";

        Id id = readId();
        int stktrcsn = buf.getInt();
        int n_elements = buf.getInt();
        Id ekid = readId();

        logger.log(Level.FINE, "HPROF_GC_OBJ_ARRAY_DUMP id " + id + " nelms " + n_elements + " ecls " + ekid);


        if (convert && currentPass == 2) {
            int sz = 4 * pointerSize + pointerSize * n_elements;
            String name = getNameForClassId(ekid);
            if (includeHeaderSize) {
                sz += pointerSize*4;
            }
            hprof_out.println("ARR " + id + " (sz=" + sz + ", trace=0, nelems=" + n_elements + ", elem type=" + name + "@" + ekid + ")");
        //hprof_out.println "ARR ${Integer.toHexString(id)} (sz=${clsdic[kid].isize}, trace=0, nelems=${n_elements}, elem type=${name[cndic[ekid]]}@${Integer.toHexString(ekid)})"
        }
        for (int i = 0; i < n_elements; i++) {
            Id val = readId();
            if (convert && currentPass == 2 && val.getValue() != 0) {
                hprof_out.println("\t[" + i + "]\t" + val);
            }
        }
        if (currentPass == 1) {
            n_HPROF_GC_OBJ_ARRAY_DUMP++;
        }
    }

    private void process_HPROF_GC_INSTANCE_DUMP() {
        String srn = "HPROF_GC_INSTANCE_DUMP";
// println "HPROF_GC_INSTANCE_DUMP"
        // id + stack trace # 
        Id id = readId();
        int stktrcn = buf.getInt();
        Id kid = readId();
        int bytes_follow = buf.getInt();

        //println "HPROF_GC_INSTANCE_DUMP ${Integer.toHexString(id)} cls ${Integer.toHexString(kid)} ${name[cndic[kid]]} ${pass}"

        logger.fine(srn + " " + id + " cls " + kid + " " + getNameForClassId(kid));
        //logger.log(Level.FINE, srn + " " + id + " cls " + kid + " " + getNameForClassId(kid));
        logger.log(Level.FINE, " D: id " + id + " kid " + kid + " follow " + bytes_follow);

        if (currentPass == 1) {
            byte[] tbuf = new byte[bytes_follow];
            buf.get(tbuf);
        } else if (currentPass == 2) {
            String cname = getNameForClassId(kid);
            if (cname == null) {
                logger.log(Level.SEVERE, "bad class name for " + kid);
            }
            if (convert && hprof_out == null) {
                logger.log(Level.SEVERE, "hprof_out is null");
            }
            if (clsDic.get(kid) == null) {
                logger.log(Level.SEVERE, "clsDic[" + kid + "] is null !");
            }
            if (convert && currentPass == 2) {
                ClassInfo ci = (ClassInfo) clsDic.get(kid);
                int isize = 0;
                if (ci != null) {
                    isize = ci.isize;
                }
                if (includeHeaderSize) {
                    isize += pointerSize*2;
                }
                hprof_out.println("OBJ " + id + " (sz=" + isize + ", trace=0, class=" + cname + "@" + kid + ")");
            //hprof_out.println "OBJ ${Integer.toHexString(id)} (sz=${clsdic[kid].isize}, trace=0, class=${cname}@${Integer.toHexString(kid)})"
            }
            Id cid = kid;
            while (cid.getValue() != 0) {
                logger.log(Level.FINE, " field dump, cid " + cid);

                ClassInfo ci = (ClassInfo) clsDic.get(cid);
                if (ci == null) {
                    logger.log(Level.SEVERE, "ci for " + cid + " is null.");
                    break;
                }
                logger.log(Level.FINE, cid.toString() + " " + ci);

                if (ci.fieldSpec != null) {
                    logger.log(Level.FINE, " fieldSpec.size " + ci.fieldSpec.size());

                    for (int i = 0; i < ci.fieldSpec.size(); i++) {
                        FieldSpec fs = (FieldSpec) ci.fieldSpec.get(i);
                        switch (fs.type) {
                            case 2: // object
                                Id val = readId();

                                if (convert && currentPass == 2 && val.getValue() != 0) {
                                    hprof_out.println("\t" + fs.name + "\t" + val);
                                }

                                if (dumpString && currentPass == 2) {
                                  if (fs.name.equals("value") && (cname.equals("java.lang.String") || cname.equals("java/lang/String"))) {
                                    char[] ca = (char[])charArrayMap.get(val);
                                    if (ca != null) {
                                      String ts = new String(ca);
                                      System.out.println("S: " + id + " " + ts);
                                      ts = null;
                                    } else {
                                      pendingStrings.put(id, val);
                                    }
                                  } 
                                }
                                break;
                            case 4: // boolean
                                buf.get();
                                break;
                            case 5: // char
                                buf.getChar();
                                break;
                            case 6: // float
                                buf.getFloat();
                                break;
                            case 7: // double
                                buf.getDouble();
                                break;
                            case 8: // byte
                                buf.get();
                                break;
                            case 9: // short
                                buf.getShort();
                                break;
                            case 10: // int
                                buf.getInt();
                                break;
                            case 11: // long
                                buf.getLong();
                                break;
                            default:
                                logger.log(Level.SEVERE, "unknown ci.fieldSpec[i].type " + fs.type);
                        }
                    }
                } else {
                    logger.log(Level.FINE, "fieldSpec is null");

                }
                cid = new Id(ci.superid);
            }
        }
        if (currentPass == 1) {
            n_HPROF_GC_INSTANCE_DUMP++;
        }
    }

    private String getNameForClassId(Id cid) {
        String name = "null";
        Id nameid = (HprofConverter.Id) cnDic.get(cid);
        if (nameid != null) {
            name = (String) nameMap.get(nameid);
        }
        return name;
    }

    private void process_HPROF_GC_CLASS_DUMP() {
        String srn = "HPROF_GC_CLASS_DUMP";
        // class id
        Id id = readId();

        String name = "null";

        logger.log(Level.FINE, srn + " " + id.toString() + " " + name);

        int stksn = buf.getInt();

        if (convert && currentPass == 1) {
            hprof_out.println("CLS " + id + " (name=" + getNameForClassId(id) + ", trace=0)");
        }

        Id superid = readId();

        if (convert && currentPass == 1 && (superid.getValue() != 0)) {
            hprof_out.println("\tsuper\t" + superid);
        }

        Id loaderid = readId();

        if (convert && currentPass == 1 && (loaderid.getValue() != 0)) {
            hprof_out.println("\tloader\t" + loaderid);
        }

        Id signersid = readId();

        Id domainid = readId();

        if (convert && currentPass == 1 && (domainid.getValue() != 0)) {
            hprof_out.println("\tdomain\t" + domainid);
        }

        readId();
        readId();

        //idx += 6*pointer_size 

        int instsize = buf.getInt();

        ClassInfo cci = null;
        if (currentPass == 1) {
            cci = new ClassInfo(superid.getValue(), instsize);
            clsDic.put(id, cci);
            //logger.log(Level.FINE, srn + " " + id + " new " + cci);    
            logger.log(Level.FINE, srn + " new " + cci);
        }

        int cpoolsize = buf.getShort();

        logger.log(Level.FINE, "id " + id + " super " + superid + " isz " + instsize + " cpsz " + cpoolsize);

        // TODO constant pool entries are not dumped
        for (int i = 0; i < cpoolsize; i++) {
            int cpidx = buf.getShort();
            int cpetype = buf.get();

            logger.log(Level.FINE, "  cp " + Integer.toHexString(cpidx) + " type " + cpetype);

            switch (cpetype) {
                case 2: // object
                    readId();
                    break;
                case 4: // boolean
                    buf.get();
                    break;
                case 5: // char
                    buf.getChar();
                    break;
                case 6: // float
                    buf.getFloat();
                    break;
                case 7: // double
                    buf.getDouble();
                    break;
                case 8: // byte
                    buf.get();
                    break;
                case 9: // short
                    buf.getShort();
                    break;
                case 10: // int
                    buf.getInt();
                    break;
                case 11: // long
                    buf.getLong();
                    break;
                default:
                    logger.log(Level.SEVERE, "ERROR: unknown constant pool entry type " + cpetype);
                    System.exit(1);
            }
        }

        int n_static_fields = buf.getShort();

        assert (n_static_fields >= 0);

        logger.log(Level.FINE, "  n_static_fields " + n_static_fields);

        for (int i = 0; i < n_static_fields; i++) {
            Id nid = readId();
            String fname = (String) nameMap.get(nid);
            byte type = buf.get();
            switch (type) {
                case 2: // object
                    Id sfid = readId();
                    logger.log(Level.FINE, String.format("  %5d sfid %x %s", i, sfid.getValue(), fname));
                    if (convert && currentPass == 1 && (sfid.getValue() != 0)) {
                        hprof_out.println("\tstatic " + fname + "\t" + sfid);
                    }
                    break;
                case 4: // boolean
                    buf.get();
                    break;
                case 5: // char
                    buf.getChar();
                    break;
                case 6: // float
                    buf.getFloat();
                    break;
                case 7: // double
                    buf.getDouble();
                    break;
                case 8: // byte
                    buf.get();
                    break;
                case 9: // short
                    buf.getShort();
                    break;
                case 10: // int
                    buf.getInt();
                    break;
                case 11: // long
                    buf.getLong();
                    break;
                default:
                    logger.log(Level.SEVERE, "ERROR: unknown static field type " + type);
            }
        }

        int n_instance_fields = buf.getShort();

        logger.log(Level.FINE, "  n_instance_fields " + n_instance_fields);

        for (int i = 0; i < n_instance_fields; i++) {
            Id fid = readId();
            String fname = (String) nameMap.get(fid);
            byte ftype = buf.get();
            logger.log(Level.FINE, String.format("  %4d %x ift %d %s", i, fid.getValue(), ftype, fname));

            if (currentPass == 1) {
                if (cci != null) {
                    cci.addFieldSpec(new FieldSpec(ftype, fname));
                }
            //clsdic[id].addFieldSpec(new FieldSpec(type: ftype, name: fname))
            }
        }
        
        if (currentPass == 1) {
            n_HPROF_GC_CLASS_DUMP++;
        }
    }

    private void process_HPROF_GC_ROOT_MONITOR_USED() {
        String srn = "HPROF_GC_ROOT_MONITOR_USED";
        Id tid = readId();
        logger.log(Level.FINE, srn + " " + tid.toString());
        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid + " (kind=<busy monitor>)");
        }
    }

    private void process_HPROF_GC_ROOT_THREAD_BLOCK() {
        String srn = "HPROF_GC_ROOT_THREAD_BLOCK";
        Id tid = readId();
        int tsn = buf.getInt();
        logger.log(Level.FINE, srn + " " + tid.toString() + " thrsn " + tsn);
        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid + " (kind=<thread block>, thread=" + tsn + ")");
        }
    }

    private void process_HPROF_GC_ROOT_STICKY_CLASS() {
        String srn = "HPROF_GC_ROOT_STICKY_CLASS";
        Id tid = readId();
        logger.log(Level.FINE, srn + " " + tid.toString());
        if (convert && currentPass == 1) {
            String name = "null";
            Id nameid = (HprofConverter.Id) cnDic.get(tid);
            if (nameid != null) {
                name = (String) nameMap.get(nameid);
            }
            hprof_out.println("ROOT " + tid + " (kind=<system class>, name=" + name + ")");
        }
    }

    private void process_HPROF_GC_ROOT_NATIVE_STACK() {
        Id tid = readId();
        int tsn = buf.getInt();
        logger.log(Level.FINE, "HPROF_GC_ROOT_NATIVE_STACK " + tid.toString() + " thrsn " + Integer.toHexString(tsn));
    }

    private void process_HPROF_GC_ROOT_JAVA_FRAME() {
        Id tid = readId();
        int tsn = buf.getInt();
        int frn = buf.getInt();
        logger.log(Level.FINE, "HPROF_GC_ROOT_JAVA_FRAME " + tid.toString() + " tsn " + Integer.toHexString(tsn) + " frn " + Integer.toHexString(frn));
        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid.toHexString() + " (kind=<Java stack>, thread=" + Integer.toHexString(tsn) + ", frame=0)");
        }
    }

    private void process_HPROF_GC_ROOT_JNI_LOCAL() {
        Id tid = readId();
        int tsn = buf.getInt();
        int frn = buf.getInt();
        logger.log(Level.FINE, "HPROF_GC_ROOT_JNI_LOCAL " + tid.toString() + " tsn " + Integer.toHexString(tsn) + " frn " + Integer.toHexString(frn));
    }

    private void process_HPROF_GC_ROOT_JNI_GLOBAL() {
        Id tid = readId();
        Id jni_gr_id = readId();
        logger.log(Level.FINE, "HPROF_GC_ROOT_JNI_GLOBAL " + tid.toString() + " grid " + jni_gr_id);

        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid.toHexString() + " (kind=<JNI global ref>, id=0, trace=0)");
        }
    }

    private void process_HPROF_GC_ROOT_THREAD_OBJ() {
        Id tid = readId();
        int tseq = buf.getInt();
        int stktrcseq = buf.getInt();
        logger.log(Level.FINE, "HPROF_GC_ROOT_THREAD_OBJ " + tid.toString());

        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid.toHexString() + " (kind=<thread>, id=" + Integer.toHexString(tseq) + ", trace=0)");
        }
    }

    private void process_HPROF_GC_ROOT_UNKNOWN() {
        Id tid = readId();

        logger.log(Level.FINE, "HPROF_GC_ROOT_UNKNOWN " + tid.toString());

        if (convert && currentPass == 1) {
            hprof_out.println("ROOT " + tid.toHexString() + " (kind=<unknown>)");
        }

    }

    private void processFile(String path, int pass) {
        currentPass = pass;
        File file = new File(path);
        currentPath = path;
        try {
            if (pass == 2 && buf != null) {
                buf.rewind();
            } else {
                RandomAccessFile raf = new RandomAccessFile(file, "r");
                buf = raf.getChannel().map(FileChannel.MapMode.READ_ONLY, 0, file.length());
            }

            readHeader(pass == 1);
            if (convert && pass == 1) {
                setupOutput();
            }

            while (buf.position() < buf.limit()) {
                byte tag = buf.get();
                int eltms = buf.getInt();
                remaining = buf.getInt();

                switch (tag) {
                    case HPROF_UTF8:
                        process_UTF8();
                        break;
                    case HPROF_LOAD_CLASS:
                        process_LOAD_CLASS();
                        break;
                    case HPROF_HEAP_DUMP:
                        process_HEAP_DUMP();
                        break;
                    default:
                        byte[] batmp = new byte[remaining];
                        buf.get(batmp);
                }
            }
        } catch (FileNotFoundException ex) {
            Logger.getLogger(HprofConverter.class.getName()).log(Level.SEVERE, null, ex);
        } catch (UnsupportedEncodingException uee) {
            Logger.getLogger(HprofConverter.class.getName()).log(Level.SEVERE, null, uee);
        } catch (IOException ioe) {
            Logger.getLogger(HprofConverter.class.getName()).log(Level.SEVERE, null, ioe);
        } finally {
            if (convert && pass == 2) {
                if (hprof_out != null) {
                    hprof_out.println("HEAP DUMP END");
                    hprof_out.flush();
                    hprof_out.close();
                }
            }
        }
    }
    
    private void printRecordStat() {
        if (logger.isLoggable(Level.INFO)) {
            System.out.println(n_HPROF_GC_CLASS_DUMP + " classes, " 
                    + n_HPROF_GC_INSTANCE_DUMP + " instances, "
                    + n_HPROF_GC_OBJ_ARRAY_DUMP + " obj arrays "
                    + n_HPROF_GC_PRIM_ARRAY_DUMP + " primitive arrays");
        }
    }

    public void processFile(String path) {
        DecimalFormat format = new DecimalFormat("#,##0.000");
        long t0 = 0;
        long t1 = 0;
        t0 = System.currentTimeMillis();
        processFile(path, 1);
        t1 = System.currentTimeMillis();
        
        if (logger.isLoggable(Level.INFO)) {
            System.out.println("pass 1 took " + format.format(((double)(t1-t0))/1000.0) + " s.");
        }
        printRecordStat();
        
        t0 = System.currentTimeMillis();
        processFile(path, 2);
        
        if (dumpString) {
          for (Iterator ite = pendingStrings.keySet().iterator(); ite.hasNext(); ) {
            Object k = ite.next();
            Id caid = (Id)pendingStrings.get(k);
            char[] ca = (char[])charArrayMap.get(caid);
            if (ca != null) {
              String ts = new String(ca);
              System.out.println("S: " + k + " " + ts);
              ts = null;
            } else {
              logger.log(Level.SEVERE, "dumpString could not find char[] " + caid + " for String " + k);
            }
          }
        }
        t1 = System.currentTimeMillis();
        if (logger.isLoggable(Level.INFO)) {
            System.out.println("pass 2 took " + format.format(((double)(t1-t0))/1000.0) + " s.");
        }
    }

    public void processFiles() {
        if (hprof_files.size() == 0) {
          showHelp();
          return;
        }
        for (Iterator ite = hprof_files.iterator(); ite.hasNext();) {
            String path = (String) ite.next();
            File f = new File(path);
            if (!f.exists()) {
                logger.log(Level.SEVERE, "file " + path + " was not found.");
                continue;
            }

            processFile(path);
        }
    }

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        HprofConverter hc = new HprofConverter();
        hc.processArgs(args);
        hc.processFiles();
    }

    class Id implements Comparable {

        long value;

        public Id(long value) {
            this.value = value;
        }

        public long getValue() {
            if (pointerSize == 4) {
                return (value & 0xffffffffL);
            } else if (pointerSize == 8) {
                return value;
            }
            throw new IllegalStateException("pointer_size " + pointerSize + " is invalid.");
        }

        public String toHexString() {
            return Long.toHexString(getValue());
        }

        public String toString() {
            return toHexString();
        }

        public int compareTo(Object a) {
          Id other = (Id)a;
          if (value < other.value) return -1;
          if (value == other.value) return 0;
          return 1;
        }

        public boolean equals(Object obj) {
            Id x = (Id) obj;
            if (value == x.value) {
                return true;
            }
            return false;
        }

        public int hashCode() {
            return (int) value;
        }
    }
    // some constants.  cf. hotspot/src/share/vm/services/heapDumper.cpp
    public static final byte HPROF_UTF8 = 0x01;
    public static final byte HPROF_LOAD_CLASS = 0x02;
    public static final byte HPROF_UNLOAD_CLASS = 0x03;
    public static final byte HPROF_FRAME = 0x04;
    public static final byte HPROF_TRACE = 0x05;
    public static final byte HPROF_ALLOC_SITES = 0x06;
    public static final byte HPROF_HEAP_SUMMARY = 0x07;
    public static final byte HPROF_START_THREAD = 0x0a;
    public static final byte HPROF_END_THREAD = 0x0b;
    public static final byte HPROF_HEAP_DUMP = 0x0c;
    public static final byte HPROF_CPU_SAMPLES = 0x0d;
    public static final byte HPROF_CONTROL_SETTINGS = 0x0e;
    public static final byte HPROF_LOCKSTATS_WAIT_TIME = 0x10;
    public static final byte HPROF_LOCKSTATS_HOLD_TIME = 0x11;
// HPROF_GC_ROOT_UNKNOWN       = 0xff
    public static final byte HPROF_GC_ROOT_UNKNOWN = -1;
    public static final byte HPROF_GC_ROOT_JNI_GLOBAL = 0x01;
    public static final byte HPROF_GC_ROOT_JNI_LOCAL = 0x02;
    public static final byte HPROF_GC_ROOT_JAVA_FRAME = 0x03;
    public static final byte HPROF_GC_ROOT_NATIVE_STACK = 0x04;
    public static final byte HPROF_GC_ROOT_STICKY_CLASS = 0x05;
    public static final byte HPROF_GC_ROOT_THREAD_BLOCK = 0x06;
    public static final byte HPROF_GC_ROOT_MONITOR_USED = 0x07;
    public static final byte HPROF_GC_ROOT_THREAD_OBJ = 0x08;
    public static final byte HPROF_GC_CLASS_DUMP = 0x20;
    public static final byte HPROF_GC_INSTANCE_DUMP = 0x21;
    public static final byte HPROF_GC_OBJ_ARRAY_DUMP = 0x22;
    public static final byte HPROF_GC_PRIM_ARRAY_DUMP = 0x23;
    public static String ascii_hprof_header = "JAVA PROFILE 1.0.1, created Sun Mar  9 20:47:24 2008\n" 
            + "\n" 
            + "Header for -agentlib:hprof (or -Xrunhprof) ASCII Output (JDK 5.0 JVMTI based)\n" 
            + "\n" 
            + "@(#)jvm.hprof.txt        1.5 06/01/28\n" 
            + "\n" 
            + " Copyright (c) 2006 Sun Microsystems, Inc. All  Rights Reserved.\n" 
            + "\n" 
            + "WARNING!  This file format is under development, and is subject to\n" 
            + "change without notice.\n" 
            + "\n" 
            + "This file contains the following types of records:\n" 
            + "\n" 
            + "THREAD START\n" 
            + "THREAD END      mark the lifetime of Java threads\n" 
            + "\n" 
            + "TRACE           represents a Java stack trace.  Each trace consists\n" 
            + "                of a series of stack frames.  Other records refer to\n" 
            + "                TRACEs to identify (1) where object allocations have\n" 
            + "                taken place, (2) the frames in which GC roots were\n" 
            + "                found, and (3) frequently executed methods.\n" 
            + "\n" 
            + "HEAP DUMP       is a complete snapshot of all live objects in the Java\n" 
            + "                heap.  Following distinctions are made:\n" 
            + "\n" 
            + "                ROOT    root set as determined by GC\n" 
            + "                CLS     classes \n" 
            + "                OBJ     instances\n" 
            + "                ARR     arrays\n" 
            + "\n" 
            + "SITES           is a sorted list of allocation sites.  This identifies\n" 
            + "                the most heavily allocated object types, and the TRACE\n" 
            + "                at which those allocations occurred.\n" 
            + "\n" 
            + "CPU SAMPLES     is a statistical profile of program execution.  The VM\n" 
            + "                periodically samples all running threads, and assigns\n" 
            + "                a quantum to active TRACEs in those threads.  Entries\n" 
            + "                in this record are TRACEs ranked by the percentage of\n" 
            + "                total quanta they consumed; top-ranked TRACEs are\n" 
            + "                typically hot spots in the program.\n" 
            + "\n" 
            + "CPU TIME        is a profile of program execution obtained by measuring\n" 
            + "                the time spent in individual methods (excluding the time\n" 
            + "                spent in callees), as well as by counting the number of\n" 
            + "                times each method is called. Entries in this record are\n" 
            + "                TRACEs ranked by the percentage of total CPU time. The\n" 
            + "                \"count\" field indicates the number of times each TRACE \n" 
            + "                is invoked.\n" 
            + "\n" 
            + "MONITOR TIME    is a profile of monitor contention obtained by measuring\n" 
            + "                the time spent by a thread waiting to enter a monitor.\n" 
            + "                Entries in this record are TRACEs ranked by the percentage\n" 
            + "                of total monitor contention time and a brief description\n" 
            + "                of the monitor.  The \"count\" field indicates the number of \n" 
            + "                times the monitor was contended at that TRACE.\n" 
            + "\n" 
            + "MONITOR DUMP    is a complete snapshot of all the monitors and threads in \n" 
            + "                the System.\n" 
            + "\n" 
            + "HEAP DUMP, SITES, CPU SAMPLES|TIME and MONITOR DUMP|TIME records are generated \n" 
            + "at program exit.  They can also be obtained during program execution by typing \n" 
            + "Ctrl-\\ (on Solaris) or by typing Ctrl-Break (on Win32).\n" 
            + "\n" 
            + "--------\n";
}

class FieldSpec {

    byte type;
    String name;

    FieldSpec(byte ftype, String fname) {
        type = ftype;
        name = fname;
    }

    public String toString() {
        return "FieldSpec{" + type + ", " + name + "}";
    }
}

class ClassInfo {

    long superid;
    int isize;
    List fieldSpec;

    public ClassInfo(long superid, int isize) {
        this.superid = superid;
        this.isize = isize;
    }

    public void addFieldSpec(FieldSpec fs) {
        if (fieldSpec == null) {
            fieldSpec = new ArrayList();
        }
        fieldSpec.add(fs);
    }

    public String toString() {
        //"ClassInfo {${Long.toHexString(superid)}, ${isize}, ${fieldSpec}}"
        StringBuilder sb = new StringBuilder();
        sb.append("ClassInfo {" + Long.toHexString(superid) + ", " + isize + ", ");
        if (fieldSpec != null) {
            for (Iterator i = fieldSpec.iterator(); i.hasNext();) {
                sb.append(i.next().toString());
                if (i.hasNext()) {
                    sb.append(", ");
                }
            }
        }
        sb.append("}");
        return sb.toString();
    }
}


