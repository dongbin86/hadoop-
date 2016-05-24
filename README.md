# hadoop-
HIVE数仓数据血缘分析工具

2015-10-27 17:10 本站整理 浏览(332)
HIVE数仓数据血缘分析工具，有需要的朋友可以参考下。



一、数仓经常会碰到的几类问题： 

1、两个数据报表进行对比，结果差异很大，需要人工核对分析指标的维度信息，比如从头分析数据指标从哪里来，处理条件是什么，最后才能分析出问题原因。 

2、基础数据表因某种原因需要修改字段，需要评估其对数仓的影响，费时费力，然后在做方案。



二、问题分析： 

数据源长途跋涉，经过大量的处理和组件来传递，呈现在业务用户面前，对数据进行回溯其实很难。元数据回溯在有效决策、策略制定、差异分析等过程中很重要。这两类问题都属于数据血缘分析问题，第一类叫做数据回溯、第二类叫做影响分析，是数据回溯的逆向。



三、解决方法： 

自己实现了一套基于hive数仓的数据血缘分析工具，来完成各个数据表、字段之间的关系梳理，进而解决上面两个问题。




工具主要目标：解析计算脚本中的HQL语句，分析得到输入输出表、输入输出字段和相应的处理条件，进行分析展现。

实现思路：对AST深度优先遍历，遇到操作的token则判断当前的操作，遇到子句则压栈当前处理，处理子句。子句处理完，栈弹出。

关键点解析： 

1、遇到TOK_TAB或TOK_TABREF则判断出当前操作的表 

2、压栈判断是否是join，判断join条件 

3、遇到TOK_WHERE判断当前where条件 

4、遇到TOK_SELEXPR判断字段的输入输出 

5、遇到TOK_SUBQUERY保存当前的子查询信息，供父查询使用 

6、遇到select *　或者未明确指出的字段，查询元数据进行辅助分析 

7、解析结果进行相关校验



代码如下：





package XXX;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.util.Map.Entry;

import org.antlr.runtime.tree.Tree;
import org.apache.hadoop.hive.ql.parse.ASTNode;
import org.apache.hadoop.hive.ql.parse.BaseSemanticAnalyzer;
import org.apache.hadoop.hive.ql.parse.HiveParser;
import org.apache.hadoop.hive.ql.parse.ParseDriver;
import org.apache.hadoop.hive.ql.parse.ParseException;

import com.xiaoju.products.exception.SQLParseException;
import com.xiaoju.products.exception.VolidateException;
import com.xiaoju.products.util.Check;
import com.xiaoju.products.util.NumberUtil;
import com.xiaoju.products.util.ParseUtil;

/**
 * hive sql解析类
 * 
 * 目的：实现HQL的语句解析，分析出输入输出表、字段和相应的处理条件。为字段级别的数据血缘提供基础。
 * 重点：获取SELECT操作中的表和列的相关操作。其他操作这判断到字段级别。
 * 实现思路：对AST深度优先遍历，遇到操作的token则判断当前的操作，遇到子句则压栈当前处理，处理子句。子句处理完，栈弹出。 
 * 关键点解析 
 *         1、遇到TOK_TAB或TOK_TABREF则判断出当前操作的表
 *         2、压栈判断是否是join，判断join条件
 *         3、遇到TOK_WHERE判断当前where条件
 *         4、遇到TOK_SELEXPR判断字段的输入输出
 *         5、遇到TOK_SUBQUERY保存当前的子查询信息，供父查询使用
 *         6、遇到select *　或者未明确指出的字段，查询元数据进行辅助分析
 *         7、解析结果进行相关校验
 *         
 * @author yangyangthomas     
 *    
 */
public class LineParser {

    private MetaDataDao dao = new MetaDataDao();
    private static final String SPLIT_DOT = ".";
    private static final String SPLIT_COMMA = ",";
    private static final String SPLIT_AND = "&";
    private static final String TOK_EOF = "<EOF>";

    private Map<String, List<ColLineParse>> subQueryMap = new HashMap<String,  List<ColLineParse>>();
    private Map<String/*table*/, List<String/*column*/>> dbMap = new HashMap<String, List<String>>();
    private List<ColLine> colLineList = new ArrayList<ColLine>(); 

    private Map<String, String> alias = new HashMap<String, String>();
    private Set<String> conditions = new HashSet<String>();
    private List<ColLineParse> cols = new ArrayList<ColLineParse>(); 
    private Set<String> outputTables = new HashSet<String>();
    private Set<String> inputTables = new HashSet<String>();

    private Stack<String> tableNameStack = new Stack<String>();
    private Stack<Oper> operStack = new Stack<Oper>();
    private Stack<Boolean> joinStack = new Stack<Boolean>();
    private Stack<ASTNode> joinOnStack = new Stack<ASTNode>();
    private int unionTimes = 0;
    private boolean isStaticUnion = true;

    private String nowQueryTable = "";
    private Oper oper ;
    private boolean joinClause = false;
    private ASTNode joinOn = null;
    private String nowQueryDB = "default";

    public List<ColLine> getColLines() {
        return colLineList;
    }
    public Set<String> getOutputTables() {
        return outputTables;
    }
    public Set<String> getInputTables() {
        return inputTables;
    }

    private enum Oper {
        SELECT, INSERT, DROP, TRUNCATE, LOAD, CREATETABLE, ALTER
    }

    private Set<String> parseIteral(ASTNode ast) {
        Set<String> set= new HashSet<String>();//当前查询所对应到的表集合
        prepareToParseCurrentNodeAndChilds(ast);
        set.addAll(parseChildNodes(ast));
        set.addAll(parseCurrentNode(ast, set));
        endParseCurrentNode(ast);
        return set;
    }

    /**
     * 解析当前节点
     * @param ast
     * @param set
     * @return
     */
    private Set<String> parseCurrentNode(ASTNode ast, Set<String> set){
        if (ast.getToken() != null) {
            switch (ast.getToken().getType()) {
            case HiveParser.TOK_CREATETABLE: //outputtable
                outputTables.add(fillDB(BaseSemanticAnalyzer.getUnescapedName((ASTNode) ast.getChild(0))));
                break;
            case HiveParser.TOK_TAB:// outputTable
                String tableTab = BaseSemanticAnalyzer.getUnescapedName((ASTNode) ast.getChild(0));
                if (oper == Oper.SELECT) {
                    nowQueryTable = tableTab;
                }
                outputTables.add(fillDB(tableTab));
                break;
            case HiveParser.TOK_TABREF:// inputTable
                ASTNode tabTree = (ASTNode) ast.getChild(0);
                String tableName = (tabTree.getChildCount() == 1) ? 
                        BaseSemanticAnalyzer.getUnescapedName((ASTNode) tabTree.getChild(0))
                        : BaseSemanticAnalyzer.getUnescapedName((ASTNode) tabTree.getChild(0))
                                + SPLIT_DOT + tabTree.getChild(1);
                if (oper == Oper.SELECT) {
                    if(joinClause && !"".equals(nowQueryTable) ){
                        nowQueryTable += SPLIT_AND + tableName;
                    }else{
                        nowQueryTable = tableName;
                    }
                    set.add(tableName);
                }
                inputTables.add(fillDB(tableName));
                if (ast.getChild(1) != null) { //(TOK_TABREF (TOK_TABNAME detail usersequence_client) c) 
                    String alia = ast.getChild(1).getText().toLowerCase();
                    alias.put(alia, tableName);
                }
                break;
            case HiveParser.TOK_SUBQUERY:
                if (ast.getChildCount() == 2) {
                    String tableAlias = unescapeIdentifier(ast.getChild(1).getText());
                    String aliaReal = "";
                    for(String table : set){
                        aliaReal+=table+SPLIT_AND;
                    }
                    if(aliaReal.length() !=0){
                        aliaReal = aliaReal.substring(0, aliaReal.length()-1);
                    }
                    alias.put(tableAlias, aliaReal);
                    putSubQueryMap(tableAlias); 
                    cols.clear();
                }
                break;

            case HiveParser.TOK_SELEXPR: //输入输出字段的处理
                 /**
                  * (TOK_DESTINATION (TOK_DIR TOK_TMP_FILE)) 
                  *     (TOK_SELECT (TOK_SELEXPR TOK_ALLCOLREF))
                  * 
                  * (TOK_DESTINATION (TOK_DIR TOK_TMP_FILE)) 
                  *     (TOK_SELECT 
                  *         (TOK_SELEXPR (. (TOK_TABLE_OR_COL p) datekey) datekey) 
                  *         (TOK_SELEXPR (TOK_TABLE_OR_COL datekey)) 
                  *         (TOK_SELEXPR (TOK_FUNCTIONDI count (. (TOK_TABLE_OR_COL base) userid)) buyer_count))
                  *         (TOK_SELEXPR (TOK_FUNCTION when (> (. (TOK_TABLE_OR_COL base) userid) 5) (. (TOK_TABLE_OR_COL base) clienttype) (> (. (TOK_TABLE_OR_COL base) userid) 1) (+ (. (TOK_TABLE_OR_COL base) datekey) 5) (+ (. (TOK_TABLE_OR_COL base) clienttype) 1)) bbbaaa)
                  */
                //解析需要插入的表
                Tree tok_insert = ast.getParent().getParent();
                Tree child = tok_insert.getChild(0).getChild(0); 
                String tName = BaseSemanticAnalyzer.getUnescapedName((ASTNode) child.getChild(0));
                String destTable = "TOK_TMP_FILE".equals(tName) ? "TOK_TMP_FILE" : fillDB(tName); 

                //select * from 的情况
                if (ast.getChild(0).getType() == HiveParser.TOK_ALLCOLREF) { 
                    String tableOrAlias = getColOrData((ASTNode) ast.getChild(0), true, false);
                    String nowTable =  fillDB(getRealTable(null, tableOrAlias));
                    String[] tableArr = nowTable.split(SPLIT_AND); //fact.test&test2
                    for (String tables : tableArr) {
                        String[] split = tables.split("\\.");
                        if (split.length > 2) {
                            throw new SQLParseException("parse table:" + nowTable);
                        }
                        String db = split.length == 2 ? split[0] : "" ;
                        String table = split.length == 2 ? split[1] : split[0] ;
                        List<String> colByTab = dao.getColumnByDBAndTable(db, table);
                        for (String column : colByTab) {
                            cols.add(new ColLineParse(destTable, column, tables + SPLIT_DOT + column, new HashSet<String>()));  
                        }
                    }
                    break;
                }

                //select c1 from t的情况
                String columnOrData = filterData(getColOrData((ASTNode)ast.getChild(0), false, false));
                //2、过滤条件的处理select类
                String condition = getCondition((ASTNode)ast.getChild(0)); 
                Set<String> clone = filterCondition(columnOrData, condition);
                String column = ast.getChild(1) != null ? parseColOrData((ASTNode)ast.getChild(1), false)
                        : parseColOrData((ASTNode)ast.getChild(0), true); //别名
                cols.add(new ColLineParse(destTable, column, columnOrData, clone)); 
                break;
            case HiveParser.TOK_WHERE: //3、过滤条件的处理select类
                conditions.add("WHERE:" + getCondition((ASTNode) ast.getChild(0)));
                break; 
            case HiveParser.TOK_ALTERTABLE_ADDPARTS:
            case HiveParser.TOK_ALTERTABLE_RENAME:
            case HiveParser.TOK_ALTERTABLE_ADDCOLS:
                ASTNode alterTableName = (ASTNode) ast.getChild(0);
                outputTables.add(alterTableName.getText() + "\t" + oper);
                break;
            default:
                /** 
                 * (or 
                 *   (> (. (TOK_TABLE_OR_COL p) orderid) (. (TOK_TABLE_OR_COL c) orderid))
                 *   (and (= (. (TOK_TABLE_OR_COL p) a) (. (TOK_TABLE_OR_COL c) b)) 
                 *        (= (. (TOK_TABLE_OR_COL p) aaa) (. (TOK_TABLE_OR_COL c) bbb))))
                 */
                 //1、过滤条件的处理join类
                if (joinOn != null && joinOn.getTokenStartIndex() == ast.getTokenStartIndex()
                        && joinOn.getTokenStopIndex() == ast.getTokenStopIndex()) {
                    ASTNode astCon = (ASTNode)ast.getChild(2);
                    conditions.add(ast.getText().substring(4) + ":" + getCondition(astCon));
                    break;  
                }
            }
        }
        return set;
    }
    /**
     * 过滤无意义条件（空、与字段相等），应用在select端
     * 如：select col1,col2+1 from table1, 此处col1的条件需要过滤
     * @param columnOrData
     * @param condition
     * @return
     */
    private Set<String> filterCondition(String columnOrData, String condition) {
        Set<String> clone = new HashSet<String>();
        if (Check.notEmpty(condition) //条件为空
                && !columnOrData.equals(condition)) { //条件和字段相等认为没有条件
            clone.add("COLFUN:" + condition);
        }
        return clone;
    }
    /**
     * 取得处理条件，主要应用在WHERE、JOIN和SELECT端
     * 如： <p>where a=1
     * <p>t1 join t2 on t1.col1=t2.col1 and t1.col2=123
     * <p>select count(distinct col1) from t1
     * @param ast
     * @return
     */
    private String getCondition(ASTNode ast) {
        if (ast.getType() == HiveParser.KW_OR
            ||ast.getType() == HiveParser.KW_AND) {
            return  "(" + getCondition((ASTNode)ast.getChild(0)) 
                    + " " + ast.getText() 
                    + " " + getCondition((ASTNode)ast.getChild(1)) + ")";
        } else if (ast.getType() == HiveParser.NOTEQUAL //判断条件  > < like in 
            || ast.getType() == HiveParser.EQUAL
            || ast.getType() == HiveParser.LESSTHAN
            || ast.getType() == HiveParser.LESSTHANOREQUALTO
            || ast.getType() == HiveParser.GREATERTHAN
            || ast.getType() == HiveParser.GREATERTHANOREQUALTO
            || ast.getType() == HiveParser.KW_LIKE
            || ast.getType() == HiveParser.DIVIDE
            || ast.getType() == HiveParser.PLUS
            || ast.getType() == HiveParser.MINUS
            || ast.getType() == HiveParser.STAR
            || ast.getType() == HiveParser.MOD
            || ast.getType() == HiveParser.AMPERSAND
            || ast.getType() == HiveParser.TILDE
            || ast.getType() == HiveParser.BITWISEOR
            || ast.getType() == HiveParser.BITWISEXOR) {
            return getColOrData((ASTNode)ast.getChild(0), false, true) 
                    + " " + ast.getText() + " " 
                    + getColOrData((ASTNode)ast.getChild(1), false, true);
        } else if (ast.getType() == HiveParser.TOK_FUNCTIONDI) {
            String condition = ast.getChild(0).getText();
            return condition + "(distinct (" + getCondition((ASTNode) ast.getChild(1)) +"))";
        } else {
            return getColOrData(ast, false, true);
        } 
    }

    /**
     * 解析when条件 
     * @param ast
     * @return case when c1>100 then col1 when c1>0 col2 else col3 end
     */
    private String getWhenCondition(ASTNode ast) {
        int cnt = ast.getChildCount();
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i < cnt; i++) {
            String condition = getCondition((ASTNode)ast.getChild(i));
            if (i == 1) {
                sb.append("case when " + condition);
            } else if (i == cnt-1) { //else
                sb.append(" else " + condition + " end");
            } else if (i % 2 == 0){ //then
                sb.append(" then " + condition);
            } else {
                sb.append(" when " + condition);
            }
        }
        return sb.toString();
    }

    /***
     *  解析when的字段信息 case when c1>100 then col1 when c1>0 col2 else col3 end
     * @param ast
     * @param isSimple 是否是简写
     * @return col1,col2,col3
     */
    private String getWhenColumn(ASTNode ast, boolean isSimple) {
        int cnt = ast.getChildCount();
        Set<String> re = new HashSet<String>();
        for (int i = 2; i < cnt; i=i+2) {
            re.add(getColOrData((ASTNode) ast.getChild(i), isSimple, false));
            if (i+1 == cnt-1) { //else
                re.add(getColOrData((ASTNode) ast.getChild(i+1), isSimple, false));
            }
        }
        StringBuilder sb = new StringBuilder();
        for (String string : re) {
            sb.append(string).append(SPLIT_COMMA);
        }
        sb.setLength(sb.length()-1);
        return sb.toString();
    }



    private void putSubQueryMap(String tableAlias) {
        putSubQueryMap(0, tableAlias); //一个sql之间不会有别名相同的情况
    }

    /**
     * 保存subQuery查询别名和字段信息
     * @param sqlIndex
     * @param tableAlias
     */
    private void putSubQueryMap(int sqlIndex, String tableAlias) {
        List<ColLineParse> list = new ArrayList<ColLineParse>();
        if (TOK_EOF.equals(tableAlias) && unionTimes > 0) { //开头是union的处理
            int size = cols.size();
            int tableNum = unionTimes + 1; //1个union,2个表
            int colNum = size / tableNum;
            for (int i = 0; i < colNum; i++) { //合并字段
                ColLineParse col = cols.get(i);
                for (int j = i + colNum; j < size; j = j + colNum) {
                    ColLineParse col2 = cols.get(j);
                    if (notNormalCol(col.getToNameParse()) && !notNormalCol(col2.getToNameParse())) {
                        col.setToNameParse(col2.getToNameParse());
                    }
                    col.addFromName(col2.getFromName());
                    Set<String> conditionSet = col2.getConditionSet();
                    conditionSet.addAll(conditions);
                    col.addConditionSet(conditionSet);
                }
                list.add(col);
            }
        } else {
            for (ColLineParse entry : cols) {
                Set<String> conditionSet = entry.getConditionSet();
                conditionSet.addAll(conditions);
                list.add(new ColLineParse(entry.getToTable(), entry.getToNameParse(), entry.getFromName(), conditionSet));
            }
        }
        String key = sqlIndex == 0 ? tableAlias : tableAlias + sqlIndex; //没有重名的情况就不用标记
        subQueryMap.put(key, list);
    }

    /**
     * 判断正常列，
     * 正常：a as col, a
     * 异常：1 ，'a' //数字、字符等作为列名
     */
    private boolean notNormalCol(String column) {
        return Check.isEmpty(column) || NumberUtil.isNumeric(column) 
                || column.startsWith("\"") || column.startsWith("\'");
    }

    /**
     * 从指定索引位置开始解析子树
     * @param ast
     * @param startIndex 开始索引
     * @param isSimple 是否简写
     * @param withCond 是否包含条件
     * @return
     */
    private String processChilds(ASTNode ast,int startIndex, boolean isSimple,
            boolean withCond) {
        StringBuilder sb = new StringBuilder();
        int cnt = ast.getChildCount();
        for (int i = startIndex; i < cnt; i++) {
            String columnOrData = getColOrData((ASTNode) ast.getChild(i), isSimple, withCond);
            if (Check.notEmpty(columnOrData)){
                sb.append(columnOrData).append(SPLIT_COMMA);
            }
        }
        if (sb.length() > 0) {
            sb.setLength(sb.length()-1);
        }
        return sb.toString();
    }   

    /***
     * 递归解析获得列名或者字符数字等
     * @param ast
     * @param isSimple 是否是简写， 如isSimple=true:col1;isSimple=false:db1.table1.col1
     * @param withCond 是否包含条件，如true:nvl(col1,0)=>nvl(col1,0);false:col1
     * @return 解析得到的列名或者字符数字等
     */
    private String getColOrData(ASTNode ast,boolean isSimple, boolean withCond) {
        if(ast.getType() == HiveParser.TOK_FUNCTIONDI 
            || ast.getType() == HiveParser.TOK_FUNCTION){
            String fun = ast.getChild(0).getText();
            String column = getColOrData((ASTNode) ast.getChild(1), isSimple, withCond);
            if ("when".equalsIgnoreCase(fun)) {
                return withCond ? getWhenCondition(ast) : getWhenColumn(ast, isSimple); 
            } else if("IN".equalsIgnoreCase(fun)) {
                String col = getColOrData((ASTNode)ast.getChild(1), false, false);
                return col + " in (" + processChilds(ast, 2, true, false) + ")";
            } else if("TOK_ISNOTNULL".equalsIgnoreCase(fun) //isnull isnotnull
                    || "TOK_ISNULL".equalsIgnoreCase(fun)){
                String col = getColOrData((ASTNode)ast.getChild(1), false, false);
                return col + " " + fun.toLowerCase().substring(4);  
            } else if("CONCAT".equalsIgnoreCase(fun) //concat
                    || "NVL".equalsIgnoreCase(fun) //NVl
                    || "date_sub".equalsIgnoreCase(fun)){
                column = processChilds(ast, 1, isSimple, withCond);
            } 
            return !withCond ? column : fun +"("+ column + ")";
        } else if(ast.getType() == HiveParser.LSQUARE){ //map,array
                String column = getColOrData((ASTNode) ast.getChild(0), isSimple, withCond);
                String key = getColOrData((ASTNode) ast.getChild(1), isSimple, withCond);
                return !withCond ?  column : column +"["+ key + "]";
        } else {
            String column = parseColOrData(ast, isSimple);
            if(Check.notEmpty(column)){
                return column;
            }
            return processChilds(ast, 0, isSimple, withCond);
        }
    }

    /**
     * 解析获得列名或者字符数字等
     * @param ast
     * @param isSimple
     * @return
     */
    private String parseColOrData(ASTNode ast, boolean isSimple) {
        if (ast.getType() == HiveParser.DOT
                && ast.getChild(0).getType() == HiveParser.TOK_TABLE_OR_COL
                && ast.getChild(0).getChildCount() == 1
                && ast.getChild(1).getType() == HiveParser.Identifier) {
            String column = BaseSemanticAnalyzer.unescapeIdentifier(ast.getChild(1)
                            .getText().toLowerCase());
            String alia = BaseSemanticAnalyzer.unescapeIdentifier(ast.getChild(0)
                            .getChild(0).getText().toLowerCase());
            String realTable = getRealTable(column, alia);
            return isSimple ? column : fillDB(realTable) + SPLIT_DOT + column;
        } else if (ast.getType() == HiveParser.TOK_TABLE_OR_COL 
                    && ast.getChildCount() == 1
                    && ast.getChild(0).getType() == HiveParser.Identifier) { 
            String column = ast.getChild(0).getText();
            return isSimple ? column : fillDB(getRealTable(column, null)) + SPLIT_DOT + column;
        } else if (ast.getType() == HiveParser.Number 
                || ast.getType() == HiveParser.StringLiteral 
                || ast.getType() == HiveParser.Identifier) {
            return ast.getText();
        }
        return null;
    }

    /**
     * 获得真实的表
     * @param column
     * @param alia
     * @return
     */
    private String getRealTable(String column, String alia) {
        String realTable = nowQueryTable;
        if (inputTables.contains(alia)) {
            realTable = alia;
        } else if (alias.get(alia) != null) {
            realTable = alias.get(alia);
        }
        if (Check.isEmpty(alia)) {
            alia = fixAlia(realTable);
        }
        if (realTable.indexOf(SPLIT_AND) > 0) {
            realTable = getSubQueryTable(column, alia ,realTable);
        } else if (Check.isEmpty(realTable)) {
            throw new SQLParseException("can't parse realTable column:" + column + ",alias:"+alia);
        }
        return realTable;
    }

    /**
     * 修正别名
     * @param alia
     * @param realTable
     * @return
     */
    private String fixAlia(String realTable) {
        for (Entry<String, String> entry : alias.entrySet()) {
            if (entry.getValue().equals(realTable)) {
                return entry.getKey();
            }
        }
        return null;
    }

    /**
     * 过滤掉无用的列：如col1,123,'2013',col2 ==>> col1,col2
     * @param col
     * @return
     */
    private String filterData(String col){
        String[] split = col.split(SPLIT_COMMA);
        StringBuilder sb = new StringBuilder();
        for (String string : split) {
            if (!notNormalCol(string)) {
                sb.append(string).append(SPLIT_COMMA);
            }
        }
        if (sb.length() > 0) {
            sb.setLength(sb.length()-1);
        }
        return sb.toString();
    }

    /**
     * 获得subquery查询中的table名称
     * @param column 对应的列
     * @param alia 别名
     * @param defaultTable 默认表名
     * @return 
     */
    private String getSubQueryTable(String column, String alia,String defaultTable) {
        List<ColLineParse> list = subQueryMap.get(alia);
        StringBuilder sb = new StringBuilder(); 
        if (Check.notEmpty(column) && Check.notEmpty(list)) {
            for (ColLineParse colLine : list) {
                if (column.equals(colLine.getToNameParse())) {
                    String fromName = colLine.getFromName(); //处理一个字段对应多个字段的情况，如union
                    sb.append(fromName.substring(0, fromName.lastIndexOf(SPLIT_DOT))).append(SPLIT_AND);
                }
            }
            if (sb.length()>0) {
                sb.setLength(sb.length()-1);
            }
        }
        return sb.length() > 0 ? sb.toString() : defaultTable;
    }

    /**
     * 解析所有子节点
     * @param ast
     * @return
     */
    private Set<String> parseChildNodes(ASTNode ast){
        Set<String> set= new HashSet<String>();
        int numCh = ast.getChildCount();
        if (numCh > 0) {
            for (int num = 0; num < numCh; num++) {
                ASTNode child = (ASTNode) ast.getChild(num);
                set.addAll(parseIteral(child));
            }
        }
        return set;
    }

    /**
     * 准备解析当前节点
     * @param ast
     */
    private void prepareToParseCurrentNodeAndChilds(ASTNode ast){
        if (ast.getToken() != null) {
            switch (ast.getToken().getType()) {
                case HiveParser.TOK_SWITCHDATABASE:
                    System.out.println("nowQueryDB changed " + nowQueryDB+ " to " +ast.getChild(0).getText());
                    nowQueryDB = ast.getChild(0).getText();
                    break;
                case HiveParser.TOK_UNION: //join 从句开始
                    if (isStaticUnion && (ast.getParent().isNil() || ast.getParent().getType() == HiveParser.TOK_UNION)) {
                        unionTimes++;
                    } else if (ast.getParent().getType() != HiveParser.TOK_UNION) {
                        isStaticUnion = false;
                    } 
                    break;
                case HiveParser.TOK_RIGHTOUTERJOIN:
                case HiveParser.TOK_LEFTOUTERJOIN:
                case HiveParser.TOK_JOIN:
                case HiveParser.TOK_LEFTSEMIJOIN:
                case HiveParser.TOK_MAPJOIN:
                case HiveParser.TOK_FULLOUTERJOIN:
                case HiveParser.TOK_UNIQUEJOIN:
                    joinStack.push(joinClause);
                    joinClause = true;
                    joinOnStack.push(joinOn);
                    joinOn = ast;
                    break;
                case HiveParser.TOK_QUERY:
                    tableNameStack.push(nowQueryTable);
                    operStack.push(oper);
                    nowQueryTable = "";//sql22
                    oper = Oper.SELECT;
                    break;
                case HiveParser.TOK_INSERT:
                    tableNameStack.push(nowQueryTable);
                    operStack.push(oper);
                    oper = Oper.INSERT;
                    break;
                case HiveParser.TOK_SELECT:
                    tableNameStack.push(nowQueryTable);
                    operStack.push(oper);
                    oper = Oper.SELECT;
                    break;
                case HiveParser.TOK_DROPTABLE:
                    oper = Oper.DROP;
                    break;
                case HiveParser.TOK_TRUNCATETABLE:
                    oper = Oper.TRUNCATE;
                    break;
                case HiveParser.TOK_LOAD:
                    oper = Oper.LOAD;
                    break;
                case HiveParser.TOK_CREATETABLE:
                    oper = Oper.CREATETABLE;
                    break;
            }
            if (ast.getToken() != null
                        && ast.getToken().getType() >= HiveParser.TOK_ALTERDATABASE_PROPERTIES
                        && ast.getToken().getType() <= HiveParser.TOK_ALTERVIEW_RENAME) {
                    oper = Oper.ALTER;
            }
        }
    }

    /**
     * 结束解析当前节点
     * @param ast
     */
    private void endParseCurrentNode(ASTNode ast){
        if (ast.getToken() != null) {
            switch (ast.getToken().getType()) { //join 从句结束，跳出join
            case HiveParser.TOK_RIGHTOUTERJOIN:
            case HiveParser.TOK_LEFTOUTERJOIN:
            case HiveParser.TOK_JOIN:
            case HiveParser.TOK_LEFTSEMIJOIN:
            case HiveParser.TOK_MAPJOIN:
            case HiveParser.TOK_FULLOUTERJOIN:
            case HiveParser.TOK_UNIQUEJOIN:
                joinClause = joinStack.pop();
                joinOn = joinOnStack.pop();
                break;
            case HiveParser.TOK_QUERY:
                break;
            case HiveParser.TOK_INSERT:
            case HiveParser.TOK_SELECT:
                nowQueryTable = tableNameStack.pop();
                oper = operStack.pop();
                break;
            }
        }
    }

    /**
     * 转义标识符
     * @param val
     * @return
     */
    private static String unescapeIdentifier(String val) {
        if (val == null) {
            return null;
        }
        if (val.charAt(0) == '`' && val.charAt(val.length() - 1) == '`') {
            val = val.substring(1, val.length() - 1);
        }
        return val;
    }

    private void parseAST(ASTNode ast) {
        parseIteral(ast);
    }

    public void parse(String sqlAll, boolean validate){
         int i = 0; //当前是第几个sql
         for (String sql : sqlAll.split("(?<!\\\\);")) {
                ParseDriver pd = new ParseDriver();
                ASTNode ast = null;
                try {
                    ast = pd.parse(sql);
                    System.out.println(ast.toStringTree());
                    parseAST(ast);
                    endParse(++i);
                } catch (ParseException e) {
                    e.printStackTrace();
                    throw new SQLParseException(e);
                }
         }

         if (validate) {
             LineValidater lineValidater = new LineValidater();
             lineValidater.validate(inputTables, outputTables, colLineList, dbMap);
         }
    }

    /**
     * 所有解析完毕之后的后期处理
     */
    private void endParse(int sqlIndex) {
        putSubQueryMap(sqlIndex, TOK_EOF); 
        putDBMap();
        setColLineList();
    }

    private void setColLineList() {
        Map<String, List<ColLineParse>> map = new HashMap<String, List<ColLineParse>>();
        for (Entry<String, List<ColLineParse>> entry : subQueryMap.entrySet()) {
            if (entry.getKey().startsWith(TOK_EOF)) {
                List<ColLineParse> value = entry.getValue();
                for (ColLineParse colLineParse : value) {
                    List<ColLineParse> list = map.get(colLineParse.getToTable());
                    if (Check.isEmpty(list)) {
                        list = new ArrayList<ColLineParse>();
                        map.put(colLineParse.getToTable(), list);
                    }
                    list.add(colLineParse);
                }
            }
        }

        for (Entry<String, List<ColLineParse>> entry : map.entrySet()) {
            String table = entry.getKey();
            List<ColLineParse> pList = entry.getValue();
            List<String> dList = dbMap.get(table);
            int metaSize = Check.isEmpty(dList) ? 0 : dList.size();
            for (int i = 0; i < pList.size(); i++) { //按顺序插入对应的字段
                ColLineParse clp = pList.get(i);
                String colName = null;
                if (i < metaSize) { 
                    colName = table + SPLIT_DOT + dList.get(i); 
                } 
                ColLine colLine = new ColLine(table, colName , clp.getToNameParse(), 
                        clp.getFromName(), clp.getConditionSet());
                colLineList.add(colLine);
            }
        }

    }

    private void putDBMap() {
        Set<String> outputTables = getOutputTables();
        for (String table : outputTables) {
            String[] pdt = ParseUtil.parseDBTable(table);
            List<String> list = dao.getColumnByDBAndTable(pdt[0], pdt[1]);
            dbMap.put(table, list);
        }
    }

    /**
     * 补全db信息
     * table1 ==>> db1.table1
     * db1.table1 ==>> db1.table1
     * db2.t1&t2 ==>> db2.t1&db1.t2
     * @param tables
     */
    private String fillDB(String nowTable) {
        StringBuilder sb = new StringBuilder();
        String[] tableArr = nowTable.split(SPLIT_AND); //fact.test&test2&test3
        for (String tables : tableArr) {
            String[] split = tables.split("\\" + SPLIT_DOT);
            if (split.length > 2) {
                System.out.println(tables);
                throw new SQLParseException("parse table:" + nowTable);
            }
            String db = split.length == 2 ? split[0] : nowQueryDB ;
            String table = split.length == 2 ? split[1] : split[0] ;
            sb.append(db).append(SPLIT_DOT).append(table).append(SPLIT_AND);
        }
        if (sb.length()>0) {
            sb.setLength(sb.length()-1);
        }
        return sb.toString();
    }
}


测试用例：



package XXX;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.hadoop.hive.ql.parse.ParseException;
import org.apache.hadoop.hive.ql.parse.SemanticException;

import junit.framework.TestCase;

public class LineParserTest extends TestCase {
    LineParser parse = new LineParser();

    /*
     * 支持解析 select * from table
     */
    public void testParseAllColumn() {
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;
        String sql1 = "use app;insert into table dest select statid from " +
                "(select * from hand_qq_passenger a join return_benefit_base_foo b on a.statid=b.id where a.channel > 10) base";
        parse.parse(sql1, true);
        inputTablesExpected.add("app.hand_qq_passenger");
        inputTablesExpected.add("app.return_benefit_base_foo");
        outputTablesExpected.add("app.dest");
        conditions.add("WHERE:app.hand_qq_passenger.channel > 10");
        conditions.add("JOIN:app.hand_qq_passenger.statid = app.return_benefit_base_foo.id");

        Set<String> clone1 = clone(conditions);
        ColLine col1 = new ColLine("statid", "app.hand_qq_passenger.statid", clone1);
        lineSetExpected.add(col1);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }   

    /*
     * 支持解析 where > and in 等
     */
    public void testParseWhere()  {
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;
        String sql1 = "INSERT OVERWRITE table app.dest PARTITION (year='2015',month='10',day='$day') " +
                "select ip,name from test where age > 10 and area in (11,22) or name<>'$V_PARYMD'";
        parse.parse(sql1, false);
        inputTablesExpected.add("default.test");
        outputTablesExpected.add("app.dest");
        conditions.add("WHERE:((default.test.age > 10 and default.test.area in (11,22)) or default.test.name <> '$V_PARYMD')");

        Set<String> clone1 = clone(conditions);
        ColLine col1 = new ColLine("ip", "default.test.ip", clone1);
        Set<String> clone2 = clone(conditions);
        ColLine col2 = new ColLine("name", "default.test.name", clone2);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }   

    /*
     * 支持join
     */
    public void testParseJoin() {
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;
        String sql = "use app;insert into table dest select nvl(a.name,0) as name, b.ip  " +
                "from test a join test1 b on a.ip=b.ip where a.age > 10 and b.area in (11,22) and to_date(b.date) > date_sub('20151001',7)";
        parse.parse(sql, false);
        inputTablesExpected.add("app.test");
        inputTablesExpected.add("app.test1");
        outputTablesExpected.add("app.dest");

        conditions.add("WHERE:((app.test.age > 10 and app.test1.area in (11,22)) and to_date(app.test1.date) > date_sub('20151001',7))");
        conditions.add("JOIN:app.test.ip = app.test1.ip");

        Set<String> clone1 = clone(conditions);
        ColLine col1 = new ColLine("ip", "app.test1.ip", clone1);
        Set<String> clone2 = clone(conditions);
        clone2.add("COLFUN:nvl(app.test.name,0)");
        ColLine col2 = new ColLine("name", "app.test.name", clone2);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
    }

    /*
     * 支持map,array
     * struct暂时不支持
     */
    public void testParseMap() {
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed; 
        String sql = "use dw;insert into table dest select 1+1 as num, params['cid'] as maptest,arr[0] as arrtest,CONCAT(year,month,day) as date " +
                "from test ";
        parse.parse(sql, false);
        inputTablesExpected.add("dw.test");
        outputTablesExpected.add("dw.dest");

        conditions.clear();
        Set<String> clone1 = clone(conditions);
        clone1.add("COLFUN:1 + 1");
        ColLine col1 = new ColLine("num", "", clone1);

        Set<String> clone2 = clone(conditions);
        clone2.add("COLFUN:dw.test.params['cid']");
        ColLine col2 = new ColLine("maptest", "dw.test.params", clone2);

        Set<String> clone3 = clone(conditions);
        clone3.add("COLFUN:dw.test.arr[0]");
        ColLine col3 = new ColLine("arrtest", "dw.test.arr", clone3);

        Set<String> clone4 = clone(conditions);
        clone4.add("COLFUN:CONCAT(dw.test.year,dw.test.month,dw.test.day)");
        ColLine col4 = new ColLine("date", "dw.test.year,dw.test.month,dw.test.day", clone4);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);
        lineSetExpected.add(col3);
        lineSetExpected.add(col4);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }

    /* *
     * 支持union 
     * <p>说明:要求sql具有可读性，没有歧义。如：
     * <p>1、尽量具有相同别名：select 1 as a, b from t1 union select 2,c from t2 =>> select 1 as a, b from t1 union select 2 as a,c as b from t2
     * <p>2、子查询中字段要列出：SELECT u.id, actions.date FROM ( SELECT av.uid AS uid FROM action_video av WHERE av.date = '2010-06-03' UNION ALL SELECT ac.uid AS uid FROM action_comment ac WHERE ac.date = '2008-06-03' ) actions JOIN users u ON (u.id = actions.uid)
     *   =>> SELECT u.id, actions.date FROM ( SELECT av.uid AS uid, av.date as date FROM action_video av WHERE av.date = '2010-06-03' UNION ALL SELECT ac.uid AS uid, ac.date as date FROM action_comment ac WHERE ac.date = '2008-06-03' ) actions JOIN users u ON (u.id = actions.uid)
     * <p>3、不写字段数要一致：select id from t1 union all select id,userName from t2
     * */
    public void testParseUnion(){
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;
        String sql = "use default;use app;SELECT u.id, actions.date FROM ( " +
                        "SELECT av.uid AS uid, av.date as date " +
                        "FROM action_video av " +
                        "WHERE av.date = '2010-06-03' " +
                        "UNION ALL " +
                        "SELECT ac.uid AS uid,ac.date as date " +
                        "FROM fact.action_comment ac " +
                        "WHERE ac.date = '2008-06-03' " +
                     ") actions JOIN users u ON (u.id = actions.uid)";
        parse.parse(sql, false);
        inputTablesExpected.add("app.users");
        inputTablesExpected.add("app.action_video");
        inputTablesExpected.add("fact.action_comment");
        outputTablesExpected.clear();

        conditions.add("WHERE:app.action_video.date = '2010-06-03'");
        conditions.add("WHERE:fact.action_comment.date = '2008-06-03'");
        conditions.add("JOIN:app.users.id = app.action_video&fact.action_comment.uid");

        Set<String> clone1 = clone(conditions);
        ColLine col1 = new ColLine("id", "app.users.id", clone1);
        Set<String> clone2 = clone(conditions);
        ColLine col2 = new ColLine("date", "app.action_video&fact.action_comment.date", clone2);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }

    public void testParseUnion2(){
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;

        String sql = "INSERT OVERWRITE TABLE target_table " +
                  "SELECT name, id, \"Category159\"  FROM source_table_1 " +
                  "UNION ALL " +
                  "SELECT name, id,category FROM source_table_2 " +
                  "UNION ALL " +
                  "SELECT name, id, \"Category160\"  FROM source_table_3 where name=123";
        parse.parse(sql, false);
        inputTablesExpected.add("default.source_table_1");
        inputTablesExpected.add("default.source_table_2");
        inputTablesExpected.add("default.source_table_3");
        outputTablesExpected.add("default.target_table");

        conditions.add("WHERE:default.source_table_3.name = 123");

        Set<String> clone1 = clone(conditions);
        ColLine col1 = new ColLine("name", "default.source_table_1.name,default.source_table_2.name,default.source_table_3.name", clone1);
        Set<String> clone2 = clone(conditions);
        ColLine col2 = new ColLine("id", "default.source_table_1.id,default.source_table_2.id,default.source_table_3.id", clone2);
        Set<String> clone3 = clone(conditions);
        clone3.add("COLFUN:\"Category159\"");
        clone3.add("COLFUN:\"Category160\"");
        ColLine col3 = new ColLine("category", "default.source_table_2.category", clone3);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);
        lineSetExpected.add(col3);

        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }



    /**
     * 支持解析
     *  <p>=,<>,>=,<=,>,<
     *  <p>join,where,case when then else end,+,-,*,/,concat,nvl
     *  <p>is null, is not null
     *  <p>sum,count,max,min,avg,distinct
     *  <p>or,and
     *  <p> to_date(last_sucgrabord_time ) > date_sub('$data_desc',7)
     *
     * @throws SemanticException
     * @throws ParseException
     */
    public void testParse() throws SemanticException, ParseException {
        Set<String> inputTablesExpected = new HashSet<String>();
        Set<String> outputTablesExpected = new HashSet<String>();
        Set<String> conditions = new HashSet<String>();
        Set<ColLine> lineSetExpected = new HashSet<ColLine>();
        Set<String> outputTablesActual;
        Set<String> inputTablesActual;
        List<ColLine> lineListActualed;

        String sql25 = "from(select p.datekey datekey, p.userid userid, c.clienttype " +
                "from detail.usersequence_client c join fact.orderpayment p on (p.orderid > c.orderid or p.a = c.b) and p.aaa=c.bbb " +
                "full outer join dim.user du on du.userid = p.userid where p.datekey = '20131118' and (du.userid in (111,222) or hash(p.test) like '%123%')) base " +
                "insert overwrite table test.customer_kpi select concat(base.datekey,1,2) as aaa, " +
                "case when base.userid > 5 then base.clienttype when base.userid > 1 then base.datekey+5 else 1-base.clienttype end bbbaaa,count(distinct hash(base.userid)) buyer_count " +
                "where base.userid is not null group by base.datekey, base.clienttype";
        parse.parse(sql25, false);
        inputTablesExpected.add("detail.usersequence_client");
        inputTablesExpected.add("fact.orderpayment");
        inputTablesExpected.add("dim.user");
        outputTablesExpected.add("test.customer_kpi");

        conditions.add("JOIN:((fact.orderpayment.orderid > detail.usersequence_client.orderid or fact.orderpayment.a = detail.usersequence_client.b) and fact.orderpayment.aaa = detail.usersequence_client.bbb)");
        conditions.add("WHERE:(fact.orderpayment.datekey = '20131118' and (dim.user.userid in (111,222) or hash(fact.orderpayment.test) like '%123%'))");
        conditions.add("WHERE:fact.orderpayment.userid isnotnull");
        conditions.add("FULLOUTERJOIN:dim.user.userid = fact.orderpayment.userid");

        Set<String> clone1 = clone(conditions);
        clone1.add("COLFUN:concat(fact.orderpayment.datekey,1,2)");
        ColLine col1 = new ColLine("aaa", "fact.orderpayment.datekey", clone1);
        Set<String> clone2 = clone(conditions);
        clone2.add("COLFUN:case when fact.orderpayment.userid > 5 then detail.usersequence_client.clienttype when fact.orderpayment.userid > 1 then fact.orderpayment.datekey + 5 else 1 - detail.usersequence_client.clienttype end");
        ColLine col2 = new ColLine("bbbaaa", "detail.usersequence_client.clienttype,detail.usersequence_client.clienttype,fact.orderpayment.datekey", clone2);
        Set<String> clone3 = clone(conditions);
        clone3.add("COLFUN:count(distinct (hash(fact.orderpayment.userid)))");
        ColLine col3 = new ColLine("buyer_count", "fact.orderpayment.userid", clone3);
        lineSetExpected.add(col1);
        lineSetExpected.add(col2);
        lineSetExpected.add(col3);
        outputTablesActual = parse.getOutputTables();
        inputTablesActual = parse.getInputTables();
        lineListActualed = parse.getColLines();
        assertSetEquals(outputTablesExpected, outputTablesActual);
        assertSetEquals(inputTablesExpected, inputTablesActual);
        assertCoLineSetEqual(lineSetExpected, lineListActualed);
        printRestult(outputTablesActual, inputTablesActual, lineListActualed);
    }



    private void assertCoLineSetEqual(Set<ColLine> lineSetExpected,
            List<ColLine> lineListActualed) {
        assertEquals(lineSetExpected.size(), lineListActualed.size());
        for (ColLine colLine : lineListActualed) {
            int i = 0;
            for (ColLine colLine2 : lineSetExpected) {
                i++;
                if (colLine.getToNameParse().equals(colLine2.getToNameParse())) {
                    assertEquals(colLine2.getFromName(), colLine.getFromName());
                    assertSetEquals(colLine2.getConditionSet(), colLine.getConditionSet());
                    i = 0;
                    break;
                } 
                if(i == lineListActualed.size()) {
                    assertFalse(true);
                }
            }
        }
    }

    private void assertSetEquals(Set<String> expected, Set<String> actual) {
        assertEquals(expected.size(), actual.size());
        for (String string : expected) {
            assertTrue(actual.contains(string));
        }
    }

    private Set<String> clone(Set<String> set){
        Set<String> list2 = new HashSet<String>(set.size());
        for (String string : set) {
            list2.add(string);
        }
        return list2;
    }

    private void printRestult(Set<String> outputTablesActual,
            Set<String> inputTablesActual, List<ColLine> lineListActualed) {
        System.out.println("inputTable:"+inputTablesActual);
        System.out.println("outputTable:"+outputTablesActual);
        for (ColLine colLine : lineListActualed) {
            System.out.println("ToTable:" + colLine.getToTable() + ",ToNameParse:" + colLine.getToNameParse() + ",ToName:" + colLine.getToName() + ",FromName:" + colLine.getFromName() + ",Condition:" + colLine.getConditionSet());
        }
    }   
}


http://tech.meituan.com/hive-sql-to-mapreduce.html 

http://www.cnblogs.com/drawwindows/p/4595771.html 

https://cwiki.apache.org/confluence/display/Hive/LanguageManual
