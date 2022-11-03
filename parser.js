const http = require('http');
const https = require('https');
const path = require('path');
const geoip = require('geoip-lite');
const inputReader = require('wait-console-input');
const { SHA3 } = require('sha3');
const md5 = require('md5');
const sqlite3 = require('sqlite3').verbose();
const express = require('express');
const session = require('express-session');
const swig = require('swig');
const ipRangeCheck = require('ip-range-check');
const bodyParser = require('body-parser');
const multer = require('multer');
const fs = require('fs');
const { JSDOM } = require('jsdom');
const jquery = require('jquery');
const diff = require('./cemerick-jsdifflib.js');
const cookieParser = require('cookie-parser');
const child_process = require('child_process');
var wikiconfig = {};  
const timeFormat = 'Y-m-d H:i:s';  // 날짜 및 시간 기본 형식
var major = 4, minor = 20, revision = 0;
const captchapng = require('captchapng');
function getTime() { return Math.floor(new Date().getTime()); };
function toDate(t) {
	var cur = getTime();
	// 초 단위 시간 구분
	if (Math.abs(cur - Math.floor(Number(t)) * 1000) < Math.abs(cur - Math.floor(Number(t)))) {
		t = Number(t) * 1000;
	}
	var date = new Date(Number(t));

	var hour = date.getUTCHours(); hour = (hour < 10 ? "0" : "") + hour;
	var min = date.getUTCMinutes(); min = (min < 10 ? "0" : "") + min;
	var sec = date.getUTCSeconds(); sec = (sec < 10 ? "0" : "") + sec;
	var year = date.getUTCFullYear();
	var month = date.getUTCMonth() + 1; month = (month < 10 ? "0" : "") + month;
	var day = date.getUTCDate(); day = (day < 10 ? "0" : "") + day;

	return year + "-" + month + "-" + day + " " + hour + ":" + min + ":" + sec;
}

function generateTime(time, fmt) {
	const d = time.split(' ')[0];
	const t = time.split(' ')[1];

	return `<time datetime="${d}T${t}.000Z" data-format="${fmt}">${time}</time>`;
}
//파서는 어려워
	function verrev(v) {
		var sp = v.split('.');
		var maj = Number(sp[0]);
		var min = Number(sp[1]);
		var rev = Number(sp[2]);

		if (major < maj) return true;
		if (major > maj) return false;
		if (minor < min) return true;
		if (minor > min) return false;
		if (revision <= rev) return true;
		if (revision > rev) return false;
		return true;
	}
function rndval(chars, length) {
	var result = '';
	var characters = chars;
	var charactersLength = characters.length;
	for (var i = 0; i < length; i++) {
		result += characters.charAt(Math.floor(Math.random() * charactersLength));
	}
	return result;
}
	const html = {
		escape(content = '') {
			if (!content) content = '';
			content = content.replace(/[&]/gi, '&amp;');
			content = content.replace(/["]/gi, '&quot;');
			content = content.replace(/[<]/gi, '&lt;');
			content = content.replace(/[>]/gi, '&gt;');

			return content;
		}
	};
const conn = new sqlite3.Database('./wikidata.db', () => 0);  // 데이터베이스
	const config = {
		getString(str, def = '') {
			if (wikiconfig[str] === undefined) {
				curs.execute("insert into config (key, value) values (?, ?)", [str, def]);
				wikiconfig[str] = def;
				return def;
			}
			return wikiconfig[str];
		}
	};
const curs = {
	execute(sql, params = []) {
		return new Promise((resolve, reject) => {
			if (sql.toUpperCase().startsWith("SELECT")) {
				conn.all(sql, params, (err, retval) => {
					if (err) return reject(err);
					conn.sd = retval;
					resolve(retval);
				});
			} else {
				conn.run(sql, params, err => {
					if (err) return reject(err);
					resolve(0);
				});
			}
		});
	}
};
	function fetchNamespaces() {
		return ['문서', '틀', '분류', '파일', '사용자', '특수기능', config.getString('wiki.site_name', '더 시드'), '토론', '휴지통', '투표'].concat(hostconfig.custom_namespaces || []);
	}
	function processTitle(d) {
		const sp = d.split(':');
		var ns = sp.length > 1 ? sp[0] : '문서';
		var title = d;
		var forceShowNamespace = false;
		var nslist = fetchNamespaces();
		if (nslist.includes(ns)) {
			title = d.replace(ns + ':', '');
			if (sp[2] !== undefined && ns == '문서' && nslist.includes(sp[1])) {
				forceShowNamespace = true;
			}
		} else {
			title = d;
			ns = '문서';
		}

		return {
			title,
			namespace: ns,
			forceShowNamespace,
			toString() {
				if (forceShowNamespace || this.namespace != '문서')
					return this.namespace + ':' + title;
				else
					return title;
			}
		};
	}
class Stack {
	constructor() {
		this.internalArray = [];
	}

	push(x) {
		return this.internalArray.push(x);
	}

	pop() {
		return this.internalArray.pop();
	}

	top() {
		return this.internalArray[this.internalArray.length - 1];
	}

	size() {
		return this.internalArray.length;
	}

	empty() {
		return !this.internalArray.length;
	}
};

module.exports.namumark = (req, content, discussion = 0, title = '', flags = '', root = '') => {
		// markdown 아니고 namumark
		flags = flags.split(' ');

		function parseTable(content) {
			var data = '\n' + content + '\n';

			// 캡션없는 표의 셀에 <td> 추가
			for (let _tr of (data.match(/^(\|\|(((?!\|\|($|\n))[\s\S])*)\|\|)$/gim) || [])) {
				var tr = _tr.match(/^(\|\|(((?!\|\|($|\n))[\s\S])*)\|\|)$/gim)[0];
				var otr = tr;
				var ntr = tr
					.replace(/^[|][|]/g, '<tr norender><td>')
					.replace(/[|][|]$/g, '</td></tr>')
					.replace(/[|][|]/g, '</td><td>')
					.replace(/\n/g, '<br />');

				data = data.replace(tr, ntr);
			}

			var datarows = data.split('\n');

			// 캡션없는 표의 시작과 끝을 감싸고, 전체에 적용되는 꾸미기 문법 적용
			for (let _tr of (data.match(/^(<tr norender><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/gim) || [])) {
				var tr = _tr.match(/^(<tr norender><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/im)[0];

				if (  // 표의 시작이라면(위에 || 문법 없음)
					(!((befrow = (datarows[datarows.findIndex(s => s == tr.split('\n')[0]) - 1] || '')).match(/^(<tr><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/im))) &&  // 이전 줄이 표가 아니면
					(!(befrow.match(/^(\|(((?!\|).)+)\|(((?!\|\|($|\n))[\s\S])*)\|\|)$/im)))  // 캡션도 아니면
				) {
					const fulloptions = (tr.replace(/&lt;((?!table).)*&gt;/g, '').match(/^<tr norender><td>((&lt;([a-z0-9 ]+)=(((?!&gt;).)+)&gt;)+)/i) || ['', ''])[1];
					var ts = '', trs = '';

					var alop, align = ((alop = (fulloptions.match(/&lt;table\s*align=(left|center|right)&gt;/))) || ['', 'left'])[1];
					if (alop) data = data.replace(tr, tr = tr.replace(alop[0], ''));

					var wiop, width = ((wiop = (fulloptions.match(/&lt;table\s*width=((\d+)(px|%|))&gt;/))) || ['', ''])[1];
					if (wiop) {
						data = data.replace(tr, tr = tr.replace(wiop[0], ''));
						trs += 'width: ' + width + '; ';
					}

					var clop, color = ((clop = (fulloptions.match(/&lt;table\s*color=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
					if (clop) {
						data = data.replace(tr, tr = tr.replace(clop[0], ''));
						trs += 'color: ' + color + '; ';
					}

					var bgop, bgcolor = ((bgop = (fulloptions.match(/&lt;table\s*bgcolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
					if (bgop) {
						data = data.replace(tr, tr = tr.replace(bgop[0], ''));
						trs += 'background-color: ' + bgcolor + '; ';
					}

					var brop, border = ((brop = (fulloptions.match(/&lt;table\s*bordercolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
					if (brop) {
						data = data.replace(tr, tr = tr.replace(brop[0], ''));
						trs += 'border: 2px solid ' + border + '; ';
					}

					if (trs) ts = ' style="' + trs + '"';

					data = data.replace(tr, '<div class="wiki-table-wrap table-' + align + '"><table class=wiki-table' + ts + '><tbody>\n' + tr);
					datarows = data.split('\n');
				} if (  // 표의 끝이라면(아래에 || 문법 없음)
					!((aftrow = (datarows[datarows.findIndex(s => s == (r = tr.split('\n'))[r.length - 1]) + 1] || '')).match(/^(<tr norender><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/im))  // 다음 줄이 표가 아니면
				) {
					data = data.replace(tr, tr + '\n</tbody></table></div>');
				}

				data = data.replace(tr, tr.replace('<tr norender>', '<tr>'));
				datarows = data.split('\n');
			}

			// 캡션있는 표 렌더링
			for (let _tr of (data.match(/^(\|(((?!\|).)+)\|(((?!\|\|($|\n))[\s\S])*)\|\|)$/gim) || [])) {
				var tr = _tr.match(/^(\|(((?!\|).)+)\|(((?!\|\|($|\n))[\s\S])*)\|\|)$/im);
				var ec = '';

				if (  // 표의 시작이 아니면 건너뛰기
					((befrow = (datarows[datarows.findIndex(s => s == tr[0].split('\n')[0]) - 1] || '')).match(/^(<tr><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/im))
				) continue; if (  // 표의 끝
					!((aftrow = (datarows[datarows.findIndex(s => s == (r = tr[0].split('\n'))[r.length - 1]) + 1] || '')).match(/^(<tr><td>(((?!<\/td><\/tr>($|\n))[\s\S])*)<\/td><\/tr>)$/im))  // 다음 줄이 표가 아니면
				) {
					ec = '\n</tbody></table></div>';
				}

				ntr = (
					('||' + tr[4] + '||')
						.replace(/^[|][|]/g, '<tr><td>')
						.replace(/[|][|]$/g, '</td></tr>')
						.replace(/[|][|]/g, '</td><td>')
						.replace(/\n/g, '<br />')
					+ ec
				);

				const fulloptions = (ntr.replace(/&lt;((?!table).)*&gt;/g, '').match(/^<tr><td>((&lt;([a-z0-9 ]+)=(((?!&gt;).)+)&gt;)+)/i) || ['', ''])[1];

				var alop, align = ((alop = (fulloptions.match(/&lt;table\s*align=(left|center|right)&gt;/))) || ['', 'left'])[1];
				if (alop) data = data.replace(ntr, ntr = ntr.replace(alop[0], ''));

				var ts = '', trs = '';

				var wiop, width = ((wiop = (fulloptions.match(/&lt;table\s*width=((\d+)(px|%|))&gt;/))) || ['', ''])[1];
				if (wiop) {
					data = data.replace(ntr, ntr = ntr.replace(wiop[0], ''));
					trs += 'width: ' + width + '; ';
				}

				var clop, color = ((clop = (fulloptions.match(/&lt;table\s*color=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
				if (clop) {
					data = data.replace(ntr, ntr = ntr.replace(clop[0], ''));
					trs += 'color: ' + color + '; ';
				}

				var bgop, bgcolor = ((bgop = (fulloptions.match(/&lt;table\s*bgcolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
				if (bgop) {
					data = data.replace(ntr, ntr = ntr.replace(bgop[0], ''));
					trs += 'background-color: ' + bgcolor + '; ';
				}

				var brop, border = ((brop = (fulloptions.match(/&lt;table\s*bordercolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/))) || ['', ''])[1];
				if (brop) {
					data = data.replace(ntr, ntr = ntr.replace(brop[0], ''));
					trs += 'border: 2px solid ' + border + '; ';
				}

				if (trs) ts = ' style="' + trs + '"';

				data = data.replace(tr[0], '<div class="wiki-table-wrap table-' + align + '"><table class=wiki-table' + ts + '><caption>' + tr[2] + '</caption><tbody>\n' + ntr);
				datarows = data.split('\n');
			}

			// 셀 꾸미기
			for (let _tr of (data.match(/^<tr>(((?!<\/tr>).)*)<\/tr>$/gim) || [])) {
				var tr = _tr.match(/^<tr>(((?!<\/tr>).)*)<\/tr>$/im)[1], ntr = tr;

				for (let td of (tr.match(/<td>(((?!<\/td>).)*)<\/td>/g) || [])) {
					var text = (td.match(/<td>(((?!<\/td>).)*)<\/td>/) || ['', ''])[1], ot = text, ntd = td;
					var notx = text.replace(/^((&lt;([a-z0-9():\| -]+)((=(((?!&gt;).)+))*)&gt;)+)/i, '');
					var attr = '', tds = '', cs = '', rs = '';

					const fulloptions = (td.replace(/(&lt;table([a-z0-9 ]+)=(((?!&gt;).)+)&gt;)/g, '').match(/^<td>((&lt;([a-z0-9():\|\^ -]+)((=(((?!&gt;).)+))*)&gt;)+)/i) || ['', ''])[1];

					// 정렬1
					if (notx.startsWith(' ') && notx.endsWith(' ')) {
						tds += 'text-align: center; ';
					}
					else if (notx.startsWith(' ') && !notx.endsWith(' ')) {
						tds += 'text-align: right; ';
					}

					// 정렬2
					var align = (fulloptions.match(/&lt;([(]|[:]|[)])&gt;/) || ['', ''])[1];

					if (align) {
						tds += 'text-align: ' + (
							align == '(' ? (
								'left'
							) : (
								align == ')' ? (
									'right'
								) : (
									'center'
								)
							)
						) + '; ';
						ntd = ntd.replace(/&lt;([(]|[:]|[)])&gt;/, '');
					}

					// 너비
					var width = (fulloptions.match(/&lt;width=((\d+)(px|%|))&gt;/) || ['', ''])[1];
					if (width) {
						tds += 'width: ' + width + '; ';
						ntd = ntd.replace(/&lt;width=((\d+)(px|%|))&gt;/, '');
					}

					// 높이
					var height = (fulloptions.match(/&lt;height=((\d+)(px|%|))&gt;/) || ['', ''])[1];
					if (height) {
						tds += 'height: ' + height + '; ';
						ntd = ntd.replace(/&lt;height=((\d+)(px|%|))&gt;/, '');
					}

					// 가로 합치기
					var colspan = (fulloptions.match(/&lt;[-](\d+)&gt;/) || ['', ''])[1];
					if (colspan) {
						cs = colspan;
						ntd = ntd.replace(/&lt;[-](\d+)&gt;/, '');
					}

					// 세로 합치기 & 정렬
					var rowopt = (fulloptions.match(/&lt;([^]|[v]|)[|](\d+)&gt;/) || ['', '', '']);
					if (rowopt[2]) {
						rs = rowopt[2];
						switch (rowopt[1]) {
							case '^':
								tds += 'vertical-align: top; ';
								break;
							case 'v':
								tds += 'vertical-align: bottom; ';
						}
						ntd = ntd.replace(/&lt;([^]|[v]|)[|](\d+)&gt;/, '');
					}

					// 셀 배경색
					var bgcolor = (fulloptions.match(/&lt;((#([a-fA-F0-9]{3,6}))|([a-zA-Z]+))&gt;/) || ['', ''])[1];
					if (bgcolor) {
						tds += 'background-color: ' + bgcolor + '; ';
						ntd = ntd.replace(/&lt;((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/, '');
					}

					// 셀 배경색 2
					var bgcolor = (fulloptions.match(/&lt;bgcolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/) || ['', ''])[1];
					if (bgcolor) {
						tds += 'background-color: ' + bgcolor + '; ';
						ntd = ntd.replace(/&lt;bgcolor=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/, '');
					}

					// 글자색
					var color = (fulloptions.match(/&lt;color=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/) || ['', ''])[1];
					if (color) {
						tds += 'color: ' + color + '; ';
						ntd = ntd.replace(/&lt;color=((#[a-fA-F0-9]{3,6})|([a-zA-Z]+))&gt;/, '');
					}

					if (tds) attr += ' style="' + tds + '"';
					if (cs) attr += ' colspan=' + cs;
					if (rs) attr += ' rowspan=' + rs;
					ntd = ntd.replace(/<td>/, '<td' + attr + '>');

					ntr = ntr.replace(td, ntd);
				}
				data = data.replace(tr, ntr)
			}

			return data
				.replace(/^\n/, '')
				.replace(/\n$/, '')
				.replace(/<tbody>\n/g, '<tbody>')
				.replace(/\n<\/tbody>/g, '<tbody>')
				.replace(/<\/tr>\n/g, '</tr>')
				.replace(/\n<tr>/g, '</tr>')
				.replace(/<\/tbody><tbody><\/tbody>/g, '</tbody>');
		}

		function multiply(a, b) {
			if (typeof a == 'number') return a * b;

			var ret = '';
			for (let i = 0; i < b; i++) ret += a;
			return ret;
		}

		var footnotes = new Stack();
		var blocks = new Stack();
		var fndisp = {};

		var fnnum = 1;
		var fnhtml = '';
		var cates = '';
		var data = content;
		var doc = processTitle(title);

		root = root || title;

		data += '\r\n';

		data = html.escape(data);
		const xref = flags.includes('backlinkinit');

		// 역링크 초기화
		if (xref)
			curs.execute("delete from backlink where title = ? and namespace = ?", [doc.title, doc.namespace]);
		const xrefl = [];

		if (!data.includes('\n') && data.includes('\r')) data = data.replace(/\r/g, '\n');
		if (data.includes('\n') && data.includes('\r')) data = data.replace(/\r\n/g, '\n');

		// 한 글자 리터럴
		for (let esc of (data.match(/(?:\\)(.)/g) || [])) {
			const match = data.match(/(?:\\)(.)/);
			data = data.replace(esc, '<spannw class=nowiki>' + match[1] + '</spannw>');
		}

		// 리터럴
		blocks = new Stack();
		let blks;
		var open = [];
		var ops = 'RENTRIPLECBRACKET' + rndval('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', 1024) + 'RENTRIPLECBRACKET';
		var cls = 'RENTRIPLECBRACKETCLOSE' + rndval('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', 1024) + 'RENTRIPLECBRACKETCLOSE';
		for (let block of (data.match(/([}][}][}]|[{][{][{](((?![}][}][}]).)*)[}][}][}]|[{][{][{](((?!}}}).)*))/gim) || [])) {
			if (block == '}}}') {
				if (!blocks.size()) continue;
				var od = data;
				data = data.replace('}}}', blocks.top() + '');
				blocks.pop();
				continue;
			}

			let h = block.match(/{{{(((?![}][}][}]).)*)/im)[1];
			if (h.match(/^[#][!]folding\s/)) {  // 접기
				blocks.push(cls);
				open.push(block);
				data = data.replace(block, ops);
			} else if (h.match(/^[#][!]html/) && !discussion) {  // HTML
				blocks.push(cls);
				open.push(block);
				data = data.replace(block, ops);
			} else if (h.match(/^[#][!]wiki\s/)) {  // 위키문법 & CSS
				blocks.push(cls);
				open.push(block);
				data = data.replace(block, ops);
			} else {  // 리터럴
				if (!block.includes('}}}')) {  // 블록
					blocks.push('</pre></nowikiblock>');
					var od = data;
					data = data.replace('{{{\n', '<nowikiblock><pre>');
					if (od == data) data = data.replace('{{{', '<nowikiblock><pre>');
				} else {  // 한 줄
					const color = h.match(/^[#]([A-Za-z0-9]+)\s/);
					const size = h.match(/^([+]|[-])([1-5])\s/);
					if (color) {
						blocks.push('}}}');
					} else if (size) {
						blocks.push('}}}');
					} else {
						data = data.replace('{{{', '<nowikiblock><code>');
						data = data.replace('}}}', '</code></nowikiblock>');
					}
					/*
						blks = new Stack();
						const block_ = block;
						for(let bl of (block_.match(/{{{(((?!({{{|}}})).)*)|}}}/))) {
							if(bl == '}}}') {
								if(!blks.size()) continue;
								block = block.replace('}}}', blks.top() + '');
								blks.pop();
								continue;
							}
							let h = bl.match(/{{{(((?![}][}][}]).)*)/im)[1];
							
							const color = h.match(/^[#]([A-Za-z0-9]+)\s/);
							const size = h.match(/^([+]|[-])([1-5])\s/);
							if(color) {
								blks.push('}}}');
							} else if(size) {
								blks.push('}}}');
							} else {
								block = block.replace('{{{', '<nowikiblock><code>');
								block = block.replace('}}}', '</code></nowikiblock>');
							}
						}
						data = data.replace(block_, block);
						*/
				}

			}
		}
		for (let blk of (data.match(RegExp(ops, 'g')) || [])) {
			data = data.replace(blk, open[0]);
			open.splice(0, 1);
		}
		data = data.replace(RegExp(cls, 'g'), '}}}');

		// 리터럴 (제대로 된 방법은 아니겠지만 이게 젤 쉬었어...)
		var { document } = (new JSDOM(data.replace(/\n/g, '<br>'))).window;
		var nwblocks = {};
		for (var item of document.querySelectorAll('nowikiblock')) {
			const key = rndval('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+=/', 2048);
			nwblocks[key] = item.innerHTML;
			item.outerHTML = key;
		}
		data = document.querySelector('body').innerHTML.replace(/<br>/g, '\n');

		// 인용문
		function parseQuotes(data) {
			const rows = data.split(/\n/);
			const rl = rows.length;
			var inquote = 0;
			for (let i = 0; i < rl; i++) {
				let row = rows[i];
				if (!row.startsWith('&gt;')) {
					if (inquote) {
						row = '</blockquotewikiquote>\n' + row;
						inquote = 0;
					}
					rows[i] = row;
					continue;
				}
				if (row.startsWith('&gt;') && !inquote) {
					row = row.replace(/^[&]gt;(\s*)/, '<blockquotewikiquote class=wiki-quote>\n');
					inquote = 1;
				} else {
					row = row.replace(/^[&]gt;(\s*)/, '');
					inquote = 1;
				}
				rows[i] = row;
			}
			if (inquote) rows.push('</blockquotewikiquote>');
			return rows.join('\n');
		} do {
			data = parseQuotes(data);
		} while (data.match(/^[&]gt;/gim));

		// 수평줄
		data = data.replace(/^[-]{4,9}$/gim, '<hr />');
		data = data.replace(/(\n{0,1})<hr \/>(\n{0,1})/g, '<hr />');

		// 인용문 마지막 처리
		data = data.replace(/<blockquotewikiquote\sclass[=]wiki[-]quote>\n/g, '<blockquote class=wiki-quote>');
		data = data.replace(/\n<\/blockquotewikiquote>/g, '</blockquote>');

		// 목록
		function parseList(data) {
			const rows = ('\n' + data + '\n').split(/\n/);
			const rl = rows.length;
			var inlist = 0;
			for (let i = 0; i < rl; i++) {
				let row = rows[i];
				if (!row.match(/^(\s+)[*]/) && !row.startsWith(' ')) {
					if (inlist) {
						row = '</liwikilist></ulwikilist>\n' + row;
						inlist = 0;
					}
					rows[i] = row;
					continue;
				}
				if (row.match(/^(\s{2,})[*]/)) {
					rows[i] = row.replace(/^(\s{2,})[*]/, ' *');
					continue;
				}
				if (row.startsWith(' *') && !inlist) {
					row = row.replace(/^\s[*](\s*)/, '<ulwikilist class=wiki-list>\n<liwikilist>\n');
					inlist = 1;
				} else {
					row = row.replace(/^\s/, '');
					row = row.replace(/^[*](\s*)/, '</liwikilist><liwikilist>\n');
					inlist = 1;
				}
				rows[i] = row;
			}
			rows.splice(0, 1);
			rows.pop();
			if (inlist) rows.push('</liwikilist>\n</ulwikilist>');
			return rows.join('\n');
		} do {
			data = parseList(data);
		} while (data.match(/^\s[*]/gim));
		data = data.replace(/<ulwikilist\sclass[=]wiki[-]list>\n/g, '<ul class=wiki-list>');
		data = data.replace(/\n<\/ulwikilist>/g, '</ul>');
		data = data.replace(/<liwikilist>\n/g, '<li>');
		data = data.replace(/\n<\/liwikilist>/g, '</li>');
		data = data.replace(/<\/liwikilist>\n<\/ulwikilist>/g, '</ul>');
		data = data.replace(/<ulwikilist\sclass[=]wiki[-]list>/g, '<ul class=wiki-list>');
		data = data.replace(/<\/ulwikilist>/g, '</ul>');
		data = data.replace(/<liwikilist>/g, '<li>');
		data = data.replace(/<\/liwikilist>/g, '</li>');

		// 들여쓰기
		function parseIndent(data) {
			const rows = data.split(/\n/);
			const rl = rows.length;
			var inindent = 0;
			for (let i = 0; i < rl; i++) {
				let row = rows[i];
				if (!row.startsWith(' ') || row.replace(/^\s/, '').startsWith('*')) {
					if (inindent) {
						row = '</divwikiindent>\n' + row;
						inindent = 0;
					}
					rows[i] = row;
					continue;
				}
				if (row.startsWith(' ') && !inindent) {
					row = row.replace(/^\s/, '<divwikiindent class=wiki-indent>\n');
					inindent = 1;
				} else {
					row = row.replace(/^\s/, '');
					inindent = 1;
				}
				rows[i] = row;
			}
			if (inindent) rows.push('</divwikiindent>');
			return rows.join('\n');
		} do {
			data = parseIndent(data);
		} while ((data.match(/^(\s+)/gim) || []).filter(item => item.replace(/\n/g, '') && item).length);
		data = data.replace(/<divwikiindent\sclass[=]wiki[-]indent>\n/g, '<div class=wiki-indent>');
		data = data.replace(/\n<\/divwikiindent>/g, '</div>');

		// 링크
		for (let link of (data.match(/\[\[(((?!\]\]).)+)\]\]/g) || [])) {
			var _dest = link.match(/\[\[(((?!\]\]).)+)\]\]/)[1].replace(/[&]amp[;]/g, '&').replace(/[&]lt[;]/g, '<').replace(/[&]gt[;]/g, '>').replace(/[&]quot[;]/g, '"');
			var dest, disp;
			if (_dest.includes('|')) {
				dest = _dest.split('|')[0];
				disp = _dest.split('|')[1];
			} else dest = disp = _dest;

			const external = dest.startsWith('http://') || dest.startsWith('https://') || dest.startsWith('ftp://');

			const dd = dest.split('#');
			if (!external) {
				if (!dd[0] && dd[1]) dd[0] = title;
				if (dest == disp) disp = dd[0];
				dest = dd[0];
			}

			var ddata = curs.execute("select content from documents where title = ? and namespace = ?", [processTitle(dest).title, processTitle(dest).namespace]);
			const notexist = !ddata.length ? ' not-exist' : '';

			if (dest.startsWith('분류:') && !discussion) {  // 분류
				cates += `<li><a href="/w/${encodeURIComponent(dest)}" class="wiki-link-internal${notexist}">${html.escape(dest.replace('분류:', ''))}</a></li>`;
				if (xref) {
					curs.execute("insert into backlink (title, namespace, link, linkns, type) values (?, ?, ?, ?, 'category')", [doc.title, doc.namespace, dest.replace('분류:', ''), '분류']);
				}
				data = data.replace(link, '');
				continue;
			} if (dest.startsWith('파일:') && !discussion && !notexist) {  // 그림
				// 나중에 구현할랭
				data = data.replace(link, '');
				continue;
			}

			dest = dest.replace(/^([:]|\s)((분류|파일)[:])/, '$2');

			const sl = dest == root ? ' wiki-self-link' : '';
			data = data.replace(link, '<a ' + (external ? 'target=_blank ' : '') + 'class="wiki-link-' + (external ? 'external' : 'internal') + '' + sl + notexist + '" href="' + (external ? '' : '/w/') + '' + (external ? html.escape : encodeURIComponent)(dest) + (!external && dd[1] ? html.escape('#' + dd[1]) : '') + '">' + html.escape(disp) + '</a>');

			// 역링크
			if (xref && !external) {
				var linkdoc = processTitle(dest);
				if (!xrefl.includes(linkdoc.title + '\n' + linkdoc.namespace)) {
					xrefl.push(linkdoc.title + '\n' + linkdoc.namespace);
					curs.execute("insert into backlink (title, namespace, link, linkns, type, exist) values (?, ?, ?, ?, 'link', ?)", [doc.title, doc.namespace, linkdoc.title, linkdoc.namespace, notexist ? '0' : '1']);
				}
			}
		}

		blocks = new Stack();
		// 삼중중괄호 서식
		for (let block of (data.match(/([}][}][}]|[{][{][{](((?![}][}][}]).)*)[}][}][}]|[{][{][{](((?!}}}).)*))/gim) || [])) {
			if (block == '}}}') {
				if (!blocks.size()) continue;
				var od = data;
				data = data.replace('}}}', blocks.top() + '');
				if (od == data) data = data.replace('\n}}}', blocks.top() + '\r');
				blocks.pop();
				continue;
			}

			var h = block.match(/{{{(((?!}}}).)*)/im)[1];

			if (h.match(/^[#][!]folding\s/)) {  // 접기
				blocks.push('</dd></dl>');
				const title = h.match(/^[#][!]folding\s(.*)$/)[1];
				data = data.replace('{{{' + h + '\n', '<dl class=wiki-folding><dt>' + title + '</dt><dd>');
			} else if (h.match(/^[#][!]wiki\s/)) {  // 위키문법 & CSS
				blocks.push('</div>');
				const style = (h.match(/style=\"(((?!\").)*)\"/) || ['', '', ''])[1];
				data = data.replace('{{{' + h + '\n', '<div style="' + style.replace(/&amp;quot;/g, '&quot;') + '">');
			} else if (h.match(/^[#][!]html/) && !discussion) {  // HTML
				if (block.includes('}}}')) {
					var rb = block;
					rb = rb.replace('}}}', '</rawhtml></nowikiblock>');
					rb = rb.replace('{{{#!html', '<nowikiblock><rawhtml>');
					data = data.replace(block, rb);
				} else {
					blocks.push('</rawhtml></nowikiblock>');
					data = data.replace('{{{#!html', '<nowikiblock><rawhtml>');
				}
			} else if (block.includes('}}}')) {  // 한 줄
				const color = h.match(/^[#]([A-Za-z0-9]+)\s/);
				const size = h.match(/^([+]|[-])([1-5])\s/);
				if (color) {  // 글자 색
					const htmlcolor = color[1].match(/^([A-Fa-f0-9]{3,6})$/);
					var col = color[1];
					if (htmlcolor) {
						col = '#' + htmlcolor[1];
					}
					data = data.replace('}}}', '</font>');
					data = data.replace('{{{' + color[0], '<font color=' + col + '>');
				} else if (size) {  // 글자 크기
					data = data.replace('}}}', '</span>');
					data = data.replace('{{{' + size[0], '<span class="wiki-size size-' + (size[1] == '+' ? 'up' : 'down') + '-' + size[2] + '">');
				}
			}
		}
		// #!html 문법
		var { document } = (new JSDOM(data.replace(/\n/g, '<br>'))).window;
		const whtags = ['br', 'hr', 'div', 'span', 'ul', 'a', 'b', 'strong', 'del', 's', 'ins', 'u', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'font', 'dl', 'dt', 'dd', 'label', 'sup', 'sub'];
		const whattr = {
			'*': ['style'],
			span: ['class'],
			a: ['href', 'class'],
			font: ['color', 'size', 'face'],
		};
		for (var item of document.querySelectorAll('rawhtml')) {
			item.innerHTML = item.textContent.replace(/\n/g, '<br>');
			for (var el of item.getElementsByTagName('*')) {
				if (whtags.includes(el.tagName.toLowerCase())) {
					for (var attr of el.attributes) {
						if (((whattr[el.tagName.toLowerCase()] || []).concat(whattr['*'])).includes(attr.name)) {
							if (attr.name == 'style') {

							}
						} else el.removeAttribute(attr.name);
					}
					switch (el.tagName.toLowerCase()) {
						case 'a':
							el.setAttribute('target', '_blank');
							if (ver('4.20.0')) {
								el.className += (el.className ? ' ' : '') + 'wiki-link-external';
							}
					}
				} else el.outerHTML = el.innerHTML;
			} item.outerHTML = item.innerHTML;
		}
		data = document.querySelector('body').innerHTML.replace(/<br>/g, '\n');

		data = data.replace(/^[#][#](.*)$/gm, '');

		// 토론 앵커
		if (discussion) for (let res of (data.match(/(\s|^)[#](\d+)(\s|$)/g) || [])) {
			const reg = res.match(/(\s|^)[#](\d+)(\s|$)/);
			data = data.replace(res, reg[1] + '<a class=wiki-self-link href="#' + reg[2] + '">#' + reg[2] + '</a>' + reg[3]);
		}

		// 문단
		data = '<div>\r' + data;
		var maxszz = 2;
		var headnum = [, 0, 0, 0, 0, 0, 0];
		var tochtml = '<div class=wiki-macro-toc id=toc>';
		var cnum = 2;
		var sec = 1;
		for (let i = 6; i; i--) {
			if (data.match(RegExp(`^${multiply('=', i)}\\s.*\\s${multiply('=', i)}$`, 'm')))
				maxszz = i;
		}
		for (let heading of (data.match(/^(=\s(((?!=).)*)\s=|==\s(((?!==).)*)\s==|===\s(((?!===).)*)\s===|====\s(((?!====).)*)\s====|=====\s(((?!=====).)*)\s=====|======\s(((?!======).)*)\s======)$/gm) || [])) {
			const hr = {};
			for (let i = 1; i <= 6; i++) {
				hr[i] = heading.match(RegExp(`^${multiply('=', i)}\\s(((?!${multiply('=', i)}).)*)\\s${multiply('=', i)}$`, 'm'));
			} for (let i = 6; i; i--) if (hr[i]) {
				if (i < cnum) for (let j = i + 1; j <= 6; j++) headnum[j] = 0;
				cnum = i;
				const title = hr[i][1];
				var snum = '';
				for (let j = i; j; j--) if (maxszz == j) {
					for (let k = j; k < i; k++)
						snum += headnum[k] + '.';
					snum += ++headnum[i];
					break;
				}
				var edlnk = '';
				if (!discussion)
					edlnk = `<span class=wiki-edit-section><a href="/edit/${encodeURIComponent(doc + '')}?section=${sec++}" rel=nofollow>[편집]</a></span>`;
				data = data.replace(heading, '</div><h' + i + ' class=wiki-heading><a href="#toc" id="s-' + snum + '">' + snum + '.</a> ' + title + edlnk + '</h' + i + '><div class=wiki-heading-content>');
				var mt = i;
				tochtml += multiply('<div class=toc-indent>', mt - maxszz + 1) + '<span class=toc-item><a href="#s-' + snum + '">' + snum + '</a>. ' + title + '</span>' + multiply('</div>', mt - maxszz + 1);
				break;
			}
		}
		tochtml += '</div>';
		data += '</div>';
		data = data.replace(/<div class=wiki[-]heading[-]content>\n/g, '<div class=wiki-heading-content>');

		// 글자 꾸미기
		if (verrev('4.7.5')) data = data.replace(/['][']['][']['](((?![']['][']['][']).)+)[']['][']['][']/g, '<strong><i>$1</i></strong>');
		data = data.replace(/['][']['](((?![']['][']).)+)[']['][']/g, '<strong>$1</strong>');
		data = data.replace(/[']['](((?!['][']).)+)['][']/g, '<i>$1</i>');
		data = data.replace(/~~(((?!~~).)+)~~/g, '<del>$1</del>');
		data = data.replace(/--(((?!--).)+)--/g, '<del>$1</del>');
		data = data.replace(/__(((?!__).)+)__/g, '<u>$1</u>');
		data = data.replace(/[,][,](((?![,][,]).)+)[,][,]/g, '<sub>$1</sub>');
		data = data.replace(/\^\^(((?!\^\^).)+)\^\^/g, '<sup>$1</sup>');

		// 글상자
		if (verrev('4.7.4'))
			data = data.replace(/{{[|](((?![|]}})(.|\n))+)[|]}}/g, '<div class=wiki-textbox>$1</div>');

		// 매크로
		data = data.replace(/\[br\]/gi, '<br />');
		data = data.replace(/\[br\((((?!\)).)*)\)\]/gi, '<br />');
		data = data.replace(/\[clearfix\]/gi, '<div style="clear: both;"></div>');
		data = data.replace(/\[clearfix\((((?!\)).)*)\)\]/gi, '<div style="clear: both;"></div>');
		data = data.replace(/\[(date|datetime)\]/gi, generateTime(toDate(getTime()), timeFormat + 'O'));
		data = data.replace(/\[(date|datetime)\((((?!\)).)*)\)\]/gi, generateTime(toDate(getTime()), timeFormat + 'O'));
		data = data.replace(/\[(tableofcontents|목차)\]/gi, tochtml);
		data = data.replace(/\[(tableofcontents|목차)\((((?!\)).)*)\)\]/gi, tochtml);

		var pgcnt = {};
		var pgcnta = 0;
		for (var ns of fetchNamespaces()) {
			const nsc = curs.execute("select count(title) from documents where namespace = ?", [ns]);
			pgcnt[ns] = nsc[0]['count(title)'];
			pgcnta += pgcnt[ns];
		}
		data = data.replace(/\[pagecount\]/gi, pgcnta);
		for (let fpcm of (data.match(/\[pagecount\((((?!\)).)*)\)\]/gi) || [])) {
			let pcm = fpcm.match(/\[pagecount\((((?!\)).)*)\)\]/i);
			data = data.replace(fpcm, pgcnt[pcm[1]] === undefined ? pgcnta : pgcnt[pcm[1]]);
		}

		// 동화상
		for (let finc of (data.match(/\[(youtube|kakaotv|nicovideo|vimeo|navertv)[(](((?![)])(.|<spannw\sclass=\"nowiki\">[)]<\/spannw>))+)[)]\]/gi) || [])) {
			let inc = finc.match(/\[(youtube|kakaotv|nicovideo|vimeo|navertv)[(](((?!([)]))(.|<spannw\sclass=\"nowiki\">[)]<\/spannw>))+)[)]\]/i);
			let vid = inc[1].replace(/<spannw\sclass=\"nowiki\">[)]<\/spannw>/, ')');
			let id = inc[2].replace(/<spannw\sclass=\"nowiki\">[)]<\/spannw>/, ')').split(',')[0].replace(/^(\s+)/, '').replace(/(\s+)$/, '').replace(/[&]quot;/g, '"').replace(/[&]amp;/g, '&').replace(/[&]lt;/g, '<').replace(/[&]gt;/g, '>');
			let paramsa = inc[2].replace(/<spannw\sclass=\"nowiki\">[)]<\/spannw>/, ')').split(',').slice(1, 99999);
			let params = {};
			for (let item of paramsa) {
				let pp = item.split('=')[0].replace(/^(\s+)/, '').replace(/(\s+)$/, '').toLowerCase();
				params[pp] = item.replace(pp + '=', '').replace(/^(\s+)/, '').replace(/(\s+)$/, '');
			}
			let d;
			switch (vid.toLowerCase()) {
				case 'youtube': {
					d = `<iframe allowfullscreen src="//www.youtube.com/embed/${encodeURIComponent(id)}${params.start ? `?start=${encodeURIComponent(params.start)}` : ''}${params.end ? ((params.start ? '&' : '?') + 'end=' + encodeURIComponent(params.end)) : ''}" loading=lazy width="${params.width || 640}" height="${params.height || 360}" frameborder=0></iframe>`;
				}
					break; case 'kakaotv': {
						d = `<iframe allowfullscreen src="//tv.kakao.com/embed/player/cliplink/${encodeURIComponent(id)}" loading=lazy width="${params.width || 640}" height="${params.height || 360}" frameborder=0></iframe>`;
					}
					break; case 'nicovideo': {
						d = `<iframe allowfullscreen src="//embed.nicovideo.jp/watch/sm${encodeURIComponent(id)}" loading=lazy width="${params.width || 720}" height="${params.height || 480}" frameborder=0></iframe>`;
					}
					break; case 'vimeo': {
						d = `<iframe allowfullscreen src="//player.vimeo.com/video/${encodeURIComponent(id)}" loading=lazy width="${params.width || 640}" height="${params.height || 360}" frameborder=0></iframe>`;
					}
					break; case 'vimeo': {
						d = `<iframe allowfullscreen src="//tv.naver.com/embed/${encodeURIComponent(id)}" loading=lazy width="${params.width || 640}" height="${params.height || 360}" frameborder=0></iframe>`;
					}
			}

			data = data.replace(finc, d);
		}

		// 틀 인클루드
		if (!flags.includes('include')) {
			for (let finc of (data.match(/\[include[(](((?![)])(.|<spannw\sclass=\"nowiki\">[)]<\/spannw>))+)[)]\]/gi) || [])) {
				let inc = finc.match(/\[include[(](((?![)])(.|<spannw\sclass=\"nowiki\">[)]<\/spannw>))+)[)]\]/i);
				let itf = inc[1].replace(/<spannw\sclass=\"nowiki\">[)]<\/spannw>/, ')').split(',')[0].replace(/^(\s+)/, '').replace(/(\s+)$/, '').replace(/[&]quot;/g, '"').replace(/[&]amp;/g, '&').replace(/[&]lt;/g, '<').replace(/[&]gt;/g, '>');
				let paramsa = inc[1].replace(/<spannw\sclass=\"nowiki\">[)]<\/spannw>/, ')').split(',').slice(1, 99999);
				let params = {};
				for (let item of paramsa) {
					let pp = item.split('=')[0].replace(/^(\s+)/, '').replace(/(\s+)$/, '').toLowerCase();
					params[pp] = item.replace(pp + '=', '').replace(/^(\s+)/, '').replace(/(\s+)$/, '');
				}
				let itd = processTitle(itf);
				let d = curs.execute("select content from documents where title = ? and namespace = ?", [itd.title, itd.namespace]);
				let acl = getacl(req, itd.title, itd.namespace, 'read', 1)
				if (!d.length || acl) {
					data = data.replace(finc, '');
					continue;
				}
				d = d[0].content;
				for (let itema of (d.match(/[@](((?![@]).)+)[@]/gi) || [])) {
					let item = itema.match(/[@](((?![@]).)+)[@]/i)[1];
					let pd = item.split('=');
					let param = pd[0].toLowerCase();
					let def = pd[1] ? item.replace(param + '=', '') : '';
					d = d.replace(itema, params[param] || def);
				}
				d = markdown(req, d, 0, itf, 'include noframe', title);
				d = d.replace(/\[include[(](((?![)]).)+)[)]\]/gi, '');

				data = data.replace(finc, d);
			}
		}

		// 각주 (1)
		const fnrows = data.split('\n');
		const frl = fnrows.length;
		for (let fi = 0; fi < frl; fi++) {
			let row = fnrows[fi];
			for (let fn of (row.match(/(\[[*](((?!\s).)*)\s|\])/g) || [])) {
				if (fn == ']') {
					if (!footnotes.size()) continue;
					row = row.replace(']', '</fnstub>');
					footnotes.pop();
					fnrows[fi] = row;
					continue;
				}
				if (!row.includes(']')) continue;
				const reg = fn.match(/(\[[*](((?!\s).)*)\s|\])/);
				row = row.replace(fn, '<fnstub' + (reg[2] ? (' name="' + reg[2] + '"') : '') + '>');
				footnotes.push('[');
				fnrows[fi] = row;
			}
		} data = fnrows.join('\n');

		// 표렌더
		var { document } = (new JSDOM(data.replace(/\n/g, '<br>'))).window;
		function ft(el) {
			const blks = el.querySelectorAll('dl.wiki-folding > dd, div.wiki-style, blockquote.wiki-quote');
			if (blks.length) for (let el2 of blks) ft(el2);
			el = (el == document ? el.querySelector('body') : el);
			const ihtml = el.innerHTML;
			el.innerHTML = parseTable(ihtml.replace(/<br>/g, '\n')).replace(/\n/g, '<br>');
		} ft(document);

		// 각주 (2)
		function ff(el) {
			const blks = el.querySelectorAll('fnstub');
			if (blks.length) for (let el2 of blks) ff(el2);
			el = (el == document ? el.querySelector('body') : el);
			el = el.querySelector('fnstub');
			if (!el) return;
			const span = document.createElement('span');
			span.innerHTML = el.innerHTML;
			el.outerHTML = `<a ${el.getAttribute('name') ? 'name="' + el.getAttribute('name') + '" ' : ''}class=wiki-fn-content title="${span.textContent}">${el.innerHTML}</a>`;
		} ff(document);

		// 각주(3)
		for (let item of document.querySelectorAll('a.wiki-fn-content')) {
			const id = item.getAttribute('name') || fnnum;
			const numid = fnnum;
			item.removeAttribute('name');
			item.setAttribute('href', '#fn-' + id);
			fnhtml += `<span class=footnote-list><span id=fn-${id} class=target></span><a href=#rfn-${numid}>[${id}]</a> ${item.innerHTML}</span>`;
			item.innerHTML = `<span id=rfn-${numid}>[${id}]`;
			fnnum++;
		}

		if (fnhtml) fnhtml = '<div class=wiki-macro-footnote>' + fnhtml + '</div>';

		// 한 글자 리터럴 처리
		for (let item of document.querySelectorAll('spannw.nowiki')) {
			item.outerHTML = item.innerHTML;
		}

		data = document.querySelector('body').innerHTML;
		data = data.replace(/\r/g, '');
		data = data.replace(/<br>/g, '\n');

		if (!discussion) data = '<div class=wiki-inner-content>' + data + '</div>';

		data = data.replace(/<div>\n/, '<div>').replace(/\n<\/div><h(\d)/g, '</div><h$1').replace(/\n/g, '<br />');

		// 사용자 문서 틀
		if (!discussion && !flags.includes('preview') && doc.namespace == '사용자') {
			const blockdata = userblocked(doc.title);
			if (blockdata) {
				data = `
				<div style="border-width: 5px 1px 1px; border-style: solid; border-color: red gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'blue\';" onmouseout="this.style.borderTopColor=\'red\';">
					<span style="font-size: 14pt;">이 사용자는 차단된 사용자입니다.${ver('4.18.0') ? ` (#${blockdata.id})` : ''}</span><br /><br />
					이 사용자는 ${generateTime(toDate(blockdata.date), timeFormat)}에 ${blockdata.expiration == '0' ? '영구적으로' : (generateTime(toDate(blockdata.expiration), timeFormat) + '까지')} 차단되었습니다.<br />
					차단 사유: ${html.escape(blockdata.note)}
				</div>
			` + data;
			}
			if (doc.namespace == '사용자') {
				if (!ver('4.0.20')) {
					if (getperm('tribune', doc.title)) {
						data = `
						<div style="border-width: 5px 1px 1px; border-style: solid; border-color: orange gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'red\';" onmouseout="this.style.borderTopColor=\'orange\';">
							<span style="font-size:14pt">이 사용자는 ${config.getString('wiki.site_name', '더 시드')}의 호민관 입니다.</span>
						</div>
					` + data;
					} if (getperm('arbiter', doc.title)) {
						data = `
						<div style="border-width: 5px 1px 1px; border-style: solid; border-color: orange gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'red\';" onmouseout="this.style.borderTopColor=\'orange\';">
							<span style="font-size:14pt">이 사용자는 ${config.getString('wiki.site_name', '더 시드')}의 중재자 입니다.</span>
						</div>
					` + data;
					} if (getperm('admin', doc.title)) {
						data = `
						<div style="border-width: 5px 1px 1px; border-style: solid; border-color: orange gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'red\';" onmouseout="this.style.borderTopColor=\'orange\';">
							<span style="font-size:14pt">이 사용자는 ${config.getString('wiki.site_name', '더 시드')}의 관리자 입니다.</span>
						</div>
					` + data;
					} if (getperm('developer', doc.title)) {
						data = `
						<div style="border-width: 5px 1px 1px; border-style: solid; border-color: purple gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'red\';" onmouseout="this.style.borderTopColor=\'purple\';">
							<span style="font-size:14pt">이 사용자는 ${config.getString('wiki.site_name', '더 시드')}의 개발자 입니다.</span>
						</div>
					` + data;
					}
				} else if (getperm('admin', doc.title)) {
					data = `
					<div style="border-width: 5px 1px 1px; border-style: solid; border-color: orange gray gray; padding: 10px; margin-bottom: 10px;" onmouseover="this.style.borderTopColor=\'red\';" onmouseout="this.style.borderTopColor=\'orange\';">
						<span style="font-size:14pt">이 사용자는 특수 권한을 가지고 있습니다.</span>
					</div>
				` + data;
				}
			}
		}

		// 각주
		if (fnhtml) data += fnhtml;

		if (!flags.includes('noframe') && !discussion && doc.namespace == '분류') {
			let content = '';

			const dbdata = curs.execute("select title, namespace, type from backlink where type = 'category' and link = ? and linkns = ?", [doc.title, doc.namespace]);
			const _nslist = dbdata.map(item => item.namespace);
			const nslistd = fetchNamespaces().filter(item => _nslist.includes(item));
			const nslist = (nslistd.includes('분류') ? ['분류'] : []).concat(nslistd.filter(item => item != '분류'));
			let nsopt = '';
			for (let ns of nslist) {
				const data = dbdata.filter(item => item.namespace == ns);
				let cnt = data.length;
				if (!cnt) continue;

				let indexes = {};
				const hj = ['ㄱ', 'ㄴ', 'ㄷ', 'ㄹ', 'ㅁ', 'ㅂ', 'ㅅ', 'ㅇ', 'ㅈ', 'ㅊ', 'ㅋ', 'ㅌ', 'ㅍ', 'ㅎ'];
				const ha = ['가', '나', '다', '라', '마', '바', '사', '아', '자', '차', '카', '타', '파', '하', String.fromCharCode(55204)];
				for (let item of data) {
					if (!item) continue;
					let chk = 0;
					for (let i = 0; i < ha.length - 1; i++) {
						const fchr = item.title[0].toUpperCase().charCodeAt(0);

						if ((hj[i].includes(item.title[0])) || (fchr >= ha[i].charCodeAt(0) && fchr < ha[i + 1].charCodeAt(0))) {
							if (!indexes[hj[i]]) indexes[hj[i]] = [];
							indexes[hj[i]].push(item);
							chk = 1;
							break;
						}
					} if (!chk) {
						if (!indexes[item.title[0].toUpperCase()]) indexes[item.title[0].toUpperCase()] = [];
						indexes[item.title[0].toUpperCase()].push(item);
					}
				}

				content += `
				<h2 class=wiki-heading>${ns == '분류' ? '하위 분류' : ('"' + doc.title + '" 분류에 속하는 ' + ns)}</h2>
				<div>전체 ${cnt}개 문서</div>
			`;

				let listc = '<div class=wiki-category-container>';
				let list = '';
				for (let idx of Object.keys(indexes).sort()) {
					list += `
					<div>
						<h3 class=wiki-heading>${html.escape(idx)}</h3>
						<ul class=wiki-list>
				`;
					for (let item of indexes[idx])
						list += `
						<li>
							<a href="/w/${encodeURIComponent(totitle(item.title, item.namespace))}">${html.escape(item.title)}</a>
						</li>
					`;
					list += '</ul></div>';
				}
				listc += list + '</div>';
				content += listc;
			}

			data += content;
		}

		if (!discussion && !flags.includes('noframe')) data = '<div class="wiki-content clearfix">' + data + '</div>';

		// 분류
		if (!flags.includes('noframe')) {
			if (cates) {
				data = `
				<div class=wiki-category>
					<h2>분류</h2>
					<ul>${cates}</ul>
				</div>
			` + data;
			} else if (doc.namespace != '사용자' && !discussion && !flags.includes('preview')) {
				data = alertBalloon('이 문서는 분류가 되어 있지 않습니다. <a href="/w/분류:분류">분류:분류</a>에서 적절한 분류를 찾아 문서를 분류해주세요!', 'info', true) + data;
			}
		}

		// 리터럴블록 복구
		for (var item in nwblocks) {
			data = data.replace(item, nwblocks[item]);
		}

		return data;
	}